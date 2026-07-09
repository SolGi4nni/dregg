let wasm_bindgen = (function(exports) {
    let script_src;
    if (typeof document !== 'undefined' && document.currentScript !== null) {
        script_src = new URL(document.currentScript.src, location.href).toString();
    }

    /**
     * A single deos-js card, driven from the browser tab over its own embedded verified
     * executor. One `CardWorld` owns one runtime with one card-cell (agent 0); its
     * affordances are fired as REAL cap-gated verified turns — the wasm realization of
     * the native [`deos_js::applet::Applet`].
     */
    class CardWorld {
        __destroy_into_raw() {
            const ptr = this.__wbg_ptr;
            this.__wbg_ptr = 0;
            CardWorldFinalization.unregister(this);
            return ptr;
        }
        free() {
            const ptr = this.__destroy_into_raw();
            wasm.__wbg_cardworld_free(ptr, 0);
        }
        /**
         * The card-cell's id (hex) — the sovereignty boundary, the agent of its turns.
         * @returns {string}
         */
        cellId() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.cardworld_cellId(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * **Fire a card affordance** — commit ONE cap-gated verified turn, then return the
         * re-read bound value (the new `bind` value the browser re-paints).
         *
         * This is `Applet::fire` in the tab. `turn` is the affordance name the web
         * renderer carried as `data-turn`; `arg` is `data-arg`. The counter card's `"inc"`
         * affordance computes its write as a pure function of the live model
         * (`count := count + arg`) and commits it through the canonical executor. An
         * unknown affordance commits nothing and errors (the native `FireError::Unknown`).
         *
         * `arg` is an `i32` so wasm-bindgen maps it to a plain JS `number` — the affordance
         * wire calls `card.fire("inc", parseInt(data-arg))`, NOT `card.fire("inc", 1n)`. (An
         * `i64` would map to a `BigInt` and the wire's plain number would throw "Cannot
         * convert N to a BigInt".) It is widened to the canonical `i64` the native
         * `Applet::fire` carries before being applied to the model.
         * @param {string} turn
         * @param {number} arg
         * @returns {bigint}
         */
        fire(turn, arg) {
            const ptr0 = passStringToWasm0(turn, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.cardworld_fire(this.__wbg_ptr, ptr0, len0, arg);
            if (ret[2]) {
                throw takeFromExternrefTable0(ret[1]);
            }
            return BigInt.asUintN(64, ret[0]);
        }
        /**
         * Mint a fresh card on its own embedded executor, seeding model `slot` to
         * `initial`. The card-cell is agent 0 (genesis) — single-custody, the same
         * posture `Applet::mint` gives the native applet (`AuthRequired::None` holder,
         * open permissions on its own cell).
         *
         * `slot` is which model field the card's `bind` reads (the counter card's
         * `{ "kind": "bind", "slot": 0 }`).
         * @param {number} slot
         * @param {bigint} initial
         */
        constructor(slot, initial) {
            const ret = wasm.cardworld_new(slot, initial);
            if (ret[2]) {
                throw takeFromExternrefTable0(ret[1]);
            }
            this.__wbg_ptr = ret[0];
            CardWorldFinalization.register(this, this.__wbg_ptr, this);
            return this;
        }
        /**
         * A witnessed read of the bound slot off the live ledger — the SAME read the
         * card's `bind` makes (`Applet::get_u64`). The value the web renderer paints
         * into the `data-slot` span.
         * @returns {bigint}
         */
        read() {
            const ret = wasm.cardworld_read(this.__wbg_ptr);
            return BigInt.asUintN(64, ret);
        }
        /**
         * The committed-receipt count — the audit tape length (one per fired turn). A
         * browser can show it to prove the fire was a real turn, not a local mutation.
         * @returns {number}
         */
        receiptCount() {
            const ret = wasm.cardworld_receiptCount(this.__wbg_ptr);
            return ret >>> 0;
        }
        /**
         * **RENDER THE COUNTER CARD TO HTML, IN-WASM** — [`Self::view_tree_json`] walked through
         * the gpui-free web renderer (`deos-view::render_html`), the live `bind` painted from the
         * committed slot ([`Self::read`]). A Custom Element sets this as its shadow root's
         * `innerHTML` and re-calls it after each `fire` to repaint. Byte-identical to the server
         * bake of the counter card at the same committed value.
         * @returns {string}
         */
        renderHtml() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.cardworld_renderHtml(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * **THE COUNTER CARD'S VIEW-TREE** — byte-for-byte the shape the SpiderMonkey engine
         * produces for the counter card (`deos.ui.vstack(text, bind, button)`): a titled column
         * with a live `bind` of the bound `slot` and a `+1` affordance `button`
         * (`{turn:"inc", arg:1}`). The SAME `{kind, props, children}` JSON the web renderer
         * (`deos-view::parse_view_tree`) consumes — [`Self::render_html`] walks it in-tab.
         * @returns {string}
         */
        viewTreeJson() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.cardworld_viewTreeJson(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
    }
    if (Symbol.dispose) CardWorld.prototype[Symbol.dispose] = CardWorld.prototype.free;
    exports.CardWorld = CardWorld;

    /**
     * The in-tab document-collaboration surface. One `DocCollabWorld` owns one runtime with one
     * **doc-cell** (agent 0) whose committed umem-heap `heap_root` IS the published document's
     * commitment. It drives the WHOLE Pijul flow — fork → diverge → stitch → a first-class conflict
     * → resolve → publish — node-less, every publish a REAL cap-gated verified turn over the
     * embedded executor leaving a receipt.
     */
    class DocCollabWorld {
        __destroy_into_raw() {
            const ptr = this.__wbg_ptr;
            this.__wbg_ptr = 0;
            DocCollabWorldFinalization.unregister(this);
            return ptr;
        }
        free() {
            const ptr = this.__destroy_into_raw();
            wasm.__wbg_doccollabworld_free(ptr, 0);
        }
        /**
         * The pending conflict's alternatives as JSON (`[{author, text}]`) — what the ConflictView
         * attributes side-by-side. Empty when there is no pending conflict.
         * @returns {string}
         */
        alternativesJson() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.doccollabworld_alternativesJson(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * **The invariant: the doc-cell's committed umem boundary EQUALS the canonical projection of
         * the published document.** When this holds, the document the algebra sees and the boundary
         * the light client trusts are the same umem (the membership/anti-forge guarantee bites).
         * @returns {boolean}
         */
        boundaryMatchesProjection() {
            const ret = wasm.doccollabworld_boundaryMatchesProjection(this.__wbg_ptr);
            return ret !== 0;
        }
        /**
         * The doc-cell's id (hex) — the document's sovereignty boundary, the agent of its turns.
         * @returns {string}
         */
        cellId() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.doccollabworld_cellId(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * The document's commitment: the doc-cell's committed umem-heap boundary `heap_root` (hex).
         * After a publish this equals `substrate_commit(published)` — the sorted-Poseidon2 root a
         * light client trusts. It MOVES on every publish (a new resolved document → a new boundary).
         * @returns {string}
         */
        commitmentHex() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.doccollabworld_commitmentHex(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * **The affordance wire** — the web renderer fires `data-turn`/`data-arg` here:
         * - `stitch` — diverge the two authors off the shared tail and merge (the pushout); a
         *   first-class conflict surfaces, held off-heap.
         * - `resolve` (`arg` = a [`ResolutionChoice`] index) — collapse the conflict with that
         *   choice's ready patch and **publish** the merged document to the umem-heap as a real
         *   verified turn.
         * Any other affordance errors (the native `FireError::Unknown`).
         * @param {string} turn
         * @param {number} arg
         */
        fire(turn, arg) {
            const ptr0 = passStringToWasm0(turn, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.doccollabworld_fire(this.__wbg_ptr, ptr0, len0, arg);
            if (ret[1]) {
                throw takeFromExternrefTable0(ret[0]);
            }
        }
        /**
         * True iff a stitched merge is currently carrying an unresolved conflict (held off-heap).
         * @returns {boolean}
         */
        hasConflict() {
            const ret = wasm.doccollabworld_hasConflict(this.__wbg_ptr);
            return ret !== 0;
        }
        /**
         * Mint a fresh doc-cell on its own embedded executor, seed the base document, and
         * **publish it to the umem-heap** (the fork point). The doc-cell is agent 0 (single-custody,
         * `AuthRequired::None` holder — the posture a card gets), funded so a metered publish turn
         * has a source. The base is published via a REAL verified turn, so the genesis boundary
         * itself leaves a receipt.
         */
        constructor() {
            const ret = wasm.doccollabworld_new();
            if (ret[2]) {
                throw takeFromExternrefTable0(ret[1]);
            }
            this.__wbg_ptr = ret[0];
            DocCollabWorldFinalization.register(this, this.__wbg_ptr, this);
            return this;
        }
        /**
         * The current PUBLISHED document's rendered text (the resolved reading) — the clean content
         * bound by the umem boundary.
         * @returns {string}
         */
        publishedText() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.doccollabworld_publishedText(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * The committed-receipt count — the audit tape length (one per published boundary, incl. the
         * genesis base publish). Proves a publish was a real verified turn, not a local poke.
         * @returns {number}
         */
        receiptCount() {
            const ret = wasm.doccollabworld_receiptCount(this.__wbg_ptr);
            return ret >>> 0;
        }
        /**
         * **THE RENDERED HTML FRAGMENT** — `view_tree_json` walked through the SAME gpui-free web
         * renderer (`deos-view::render_html`) the cockpit's web projection bakes. The live page sets
         * this as the doc container's `innerHTML`, re-rendering WHOLESALE after every affordance
         * (the tree SHAPE changes: the ConflictView collapses to the clean published document — a
         * slot-repaint would not suffice).
         * @returns {string}
         */
        viewHtml() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.doccollabworld_viewHtml(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * **THE DOCUMENT VIEW-TREE** — the `{kind, props, children}` JSON the web renderer
         * (`deos-view::parse_view_tree`) consumes. When a conflict is held it is a ConflictView
         * (the clean prefix, the two alternatives attributed side-by-side, and a resolution `Button`
         * per [`ResolutionChoice`]); when published it is the clean resolved document plus the umem
         * boundary readout and a `stitch` affordance.
         * @returns {string}
         */
        viewTreeJson() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.doccollabworld_viewTreeJson(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
    }
    if (Symbol.dispose) DocCollabWorld.prototype[Symbol.dispose] = DocCollabWorld.prototype.free;
    exports.DocCollabWorld = DocCollabWorld;

    /**
     * The reflective-inspector card, driven from the browser tab over its own embedded verified
     * executor. One `InspectorWorld` owns one runtime with one focused card-cell (agent 0); its
     * view-tree is generated from that cell's REAL faces ([`Self::view_tree_json`]) and its
     * affordances fire as REAL cap-gated verified turns — the wasm realization of the native
     * [`deos_js::inspector_card`] over a live World.
     */
    class InspectorWorld {
        __destroy_into_raw() {
            const ptr = this.__wbg_ptr;
            this.__wbg_ptr = 0;
            InspectorWorldFinalization.unregister(this);
            return ptr;
        }
        free() {
            const ptr = this.__destroy_into_raw();
            wasm.__wbg_inspectorworld_free(ptr, 0);
        }
        /**
         * The focused cell's balance (a structural substance the RawFields face shows) — a
         * witnessed read for the live status strip.
         * @returns {bigint}
         */
        balance() {
            const ret = wasm.inspectorworld_balance(this.__wbg_ptr);
            return ret;
        }
        /**
         * The focused card-cell's id (hex) — the sovereignty boundary, the agent of its turns.
         * @returns {string}
         */
        cellId() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.inspectorworld_cellId(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * **Fire one of the focused cell's affordances** — commit ONE cap-gated verified turn on
         * the live World (exactly what a rendered affordance `Button`'s click does), then return
         * the re-read value of the slot it advanced (the new `Bind` value the browser re-paints).
         *
         * `turn` is the affordance name the web renderer carried as `data-turn`; `arg` is
         * `data-arg`. The inspector card's affordances each advance one bound slot as a pure
         * function of the live model (so the bound row updates in place) and commit it through the
         * canonical executor, leaving a real receipt. An unknown affordance commits nothing and
         * errors (the native `FireError::Unknown`).
         *
         * `arg` is an `i32` (maps to a plain JS `number`, not a `BigInt`) — the affordance wire
         * calls `card.fire("tick", parseInt(data-arg))`. Widened to the canonical `i64` before it
         * touches the model.
         * @param {string} turn
         * @param {number} arg
         * @returns {bigint}
         */
        fire(turn, arg) {
            const ptr0 = passStringToWasm0(turn, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.inspectorworld_fire(this.__wbg_ptr, ptr0, len0, arg);
            if (ret[2]) {
                throw takeFromExternrefTable0(ret[1]);
            }
            return BigInt.asUintN(64, ret[0]);
        }
        /**
         * Mint a fresh inspector card on its own embedded executor, focused on a genesis
         * card-cell with a few seeded scalar state slots (so the RawFields face shows live
         * `Bind` rows). The cell is agent 0 (single-custody, `AuthRequired::None` holder — the
         * posture `Applet::mint` gives a card), funded so a metered turn has a source.
         *
         * `seeds[i]` seeds [`INSPECTOR_FIELD_SLOTS`]`[i]` (clamped to the available slots); each
         * seed is committed via a REAL verified turn (no out-of-band poke), so the genesis state
         * itself leaves receipts. Pass an empty/short array to seed the defaults.
         * @param {BigUint64Array} seeds
         */
        constructor(seeds) {
            const ptr0 = passArray64ToWasm0(seeds, wasm.__wbindgen_malloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.inspectorworld_new(ptr0, len0);
            if (ret[2]) {
                throw takeFromExternrefTable0(ret[1]);
            }
            this.__wbg_ptr = ret[0];
            InspectorWorldFinalization.register(this, this.__wbg_ptr, this);
            return this;
        }
        /**
         * The focused cell's nonce (the turn counter — another structural substance). Advances by
         * one per fired affordance (each turn carries an `IncrementNonce`).
         * @returns {bigint}
         */
        nonce() {
            const ret = wasm.inspectorworld_nonce(this.__wbg_ptr);
            return BigInt.asUintN(64, ret);
        }
        /**
         * A witnessed read of model `slot` off the live ledger — the SAME read the inspector's
         * `Bind` row makes (`Applet::get_u64`). The value the web renderer paints into the
         * matching `data-slot` span. (Takes a `slot` arg — the inspector binds SEVERAL slots,
         * unlike the single-slot counter `CardWorld::read`.)
         * @param {number} slot
         * @returns {bigint}
         */
        read(slot) {
            const ret = wasm.inspectorworld_read(this.__wbg_ptr, slot);
            return BigInt.asUintN(64, ret);
        }
        /**
         * The committed-receipt count — the audit tape length (one per fired turn, plus the
         * genesis seeds). A browser shows it to prove a fire was a real turn, not a local poke.
         * @returns {number}
         */
        receiptCount() {
            const ret = wasm.inspectorworld_receiptCount(this.__wbg_ptr);
            return ret >>> 0;
        }
        /**
         * **RENDER THE INSPECTOR CARD TO HTML, IN-WASM** — [`Self::view_tree_json`] walked through
         * the gpui-free web renderer, each live `Bind` row painted from its own slot off the
         * committed ledger ([`Self::read`]). The Custom Element repaints via this after each fire.
         * @returns {string}
         */
        renderHtml() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.inspectorworld_renderHtml(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * **THE INSPECTOR VIEW-TREE, GENERATED FROM THE LIVE CELL'S FACES.** Reads the focused
         * cell's RawFields + Affordances faces off the live ledger (via [`deos_reflect`], the
         * SAME substrate the native `inspector_view_for` reads) and lifts them into the view-tree
         * JSON the web renderer (`deos-view`) parses: a titled column with a "Cell State" section
         * (a `Bind` row per revealed scalar slot, a `Text` per structural substance) and an
         * "Affordances" section (a `Button` per affordance the holder may fire). This is the
         * inspector card's `view_source` — serve it to the renderer and the focused cell's faces
         * paint live in a browser. Regenerate after a fire and a newly-non-zero slot appears as a
         * fresh `Bind` row (the reflective view tracks the live state).
         * @returns {string}
         */
        viewTreeJson() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.inspectorworld_viewTreeJson(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
    }
    if (Symbol.dispose) InspectorWorld.prototype[Symbol.dispose] = InspectorWorld.prototype.free;
    exports.InspectorWorld = InspectorWorld;

    /**
     * The KV-store service cell, driven from the browser tab. A `KvStoreWorld` owns one runtime
     * with a CALLER agent (agent 0, the signer/fee-payer) and a separate STORE cell carrying the
     * published interface + the verified `CellProgram`. Each `put`/`delete` affordance is ROUTED
     * through the store's `InterfaceDescriptor` and fired as a REAL cap-gated verified turn
     * against the store cell — the wasm realization of `starbridge_kvstore` over a live World.
     */
    class KvStoreWorld {
        __destroy_into_raw() {
            const ptr = this.__wbg_ptr;
            this.__wbg_ptr = 0;
            KvStoreWorldFinalization.unregister(this);
            return ptr;
        }
        free() {
            const ptr = this.__destroy_into_raw();
            wasm.__wbg_kvstoreworld_free(ptr, 0);
        }
        /**
         * The store cell's id (hex) — the service object's sovereignty boundary.
         * @returns {string}
         */
        cellId() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.kvstoreworld_cellId(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * **Invoke `delete(reg)`** — clear `reg` to zero and bump the store version, as a REAL
         * cap-gated verified turn routed through the interface. Returns the re-read value (0).
         * @param {number} reg
         * @returns {bigint}
         */
        delete(reg) {
            const ret = wasm.kvstoreworld_delete(this.__wbg_ptr, reg);
            if (ret[2]) {
                throw takeFromExternrefTable0(ret[1]);
            }
            return BigInt.asUintN(64, ret[0]);
        }
        /**
         * **The affordance wire entry** — the web renderer fires `data-turn`/`data-arg` here.
         * `put`/`delete` route + commit; any other name errors (the native `FireError::Unknown`).
         * `arg` is the register index the button carried.
         * @param {string} turn
         * @param {number} arg
         * @returns {bigint}
         */
        fire(turn, arg) {
            const ptr0 = passStringToWasm0(turn, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.kvstoreworld_fire(this.__wbg_ptr, ptr0, len0, arg);
            if (ret[2]) {
                throw takeFromExternrefTable0(ret[1]);
            }
            return BigInt.asUintN(64, ret[0]);
        }
        /**
         * The published interface as JSON (`[{name, auth, semantics, arity}]`) — what the Service
         * Explorer resolves. The card shows it so a visitor sees the typed contract the affordances
         * route through.
         * @returns {string}
         */
        methodsJson() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.kvstoreworld_methodsJson(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * Mint a KV-store on its own embedded executor: a caller agent (the signer), a store cell
         * owned by a distinct synthetic key with the [`app_programs::kvstore_program`] installed
         * (open permissions; the verified slot-caveat is the enforcement), and a reach capability
         * granted to the caller. `seeds[i]` seeds register [`app_programs::KV_REG_MIN`]`+ i` via a
         * REAL `put` invocation (each routes through the interface and bumps the version), so the
         * genesis store itself leaves receipts. Pass an empty/short array for the defaults.
         * @param {BigUint64Array} seeds
         */
        constructor(seeds) {
            const ptr0 = passArray64ToWasm0(seeds, wasm.__wbindgen_malloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.kvstoreworld_new(ptr0, len0);
            if (ret[2]) {
                throw takeFromExternrefTable0(ret[1]);
            }
            this.__wbg_ptr = ret[0];
            KvStoreWorldFinalization.register(this, this.__wbg_ptr, this);
            return this;
        }
        /**
         * **Invoke `put(reg)`** — write `reg := reg + 1` (a single-arg-friendly bump) and bump the
         * store version by one, as a REAL cap-gated verified turn ROUTED through the published
         * interface. Returns the re-read register value. `value` (when ≥ 0) overrides the written
         * value (used by the seed path); a negative `value` means "bump the current register".
         * @param {number} reg
         * @param {number} value
         * @returns {bigint}
         */
        put(reg, value) {
            const ret = wasm.kvstoreworld_put(this.__wbg_ptr, reg, value);
            if (ret[2]) {
                throw takeFromExternrefTable0(ret[1]);
            }
            return BigInt.asUintN(64, ret[0]);
        }
        /**
         * A witnessed read of store slot `slot` off the live ledger (the canonical felt lane). The
         * value the web renderer paints into the matching `data-slot` span — slot 0 is the version,
         * slots `REG_MIN..` the registers.
         * @param {number} slot
         * @returns {bigint}
         */
        read(slot) {
            const ret = wasm.kvstoreworld_read(this.__wbg_ptr, slot);
            return BigInt.asUintN(64, ret);
        }
        /**
         * The committed-receipt count — the audit tape length (one per committed method turn,
         * including the genesis seed puts).
         * @returns {number}
         */
        receiptCount() {
            const ret = wasm.kvstoreworld_receiptCount(this.__wbg_ptr);
            return ret >>> 0;
        }
        /**
         * **RENDER THE KV-STORE CARD TO HTML, IN-WASM** — [`Self::view_tree_json`] (the version row
         * + a `Table` of register rows) walked through the gpui-free web renderer, each live `bind`
         * painted from its own slot off the committed ledger ([`Self::read`] over the canonical
         * big-endian felt lane). The Custom Element repaints via this after each `put`/`del` fire.
         * @returns {string}
         */
        renderHtml() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.kvstoreworld_renderHtml(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * **Prove `get` is a NAMED SEAM, not a faked write** — route `get(reg)` through the
         * interface; because it is `Semantics::Serviced` its answer rides the OFE cross-cell-read,
         * so the router REFUSES to desugar it to a turn. Returns the refusal message (the honest
         * seam), or — never reached for a correct descriptor — an error if `get` somehow desugared.
         * @param {number} reg
         * @returns {string}
         */
        tryGet(reg) {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.kvstoreworld_tryGet(this.__wbg_ptr, reg);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * **Prove the verified guarantee BITES in the tab** — attempt a `put` that LOWERS the
         * store version (a replay/rollback), which the store program's `Monotonic` version
         * constraint must REFUSE on the verified commit path. Returns JSON
         * `{refused: bool, reason: string}`; `refused: true` is the witnessed enforcement. (Needs
         * the version already ≥ 1 — seed the store first.)
         * @param {number} reg
         * @returns {string}
         */
        tryRollback(reg) {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.kvstoreworld_tryRollback(this.__wbg_ptr, reg);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * The store's monotone version (slot 0) — bumped by every committed `put`/`delete`, and
         * (by the verified `Monotonic` constraint) never able to roll back.
         * @returns {bigint}
         */
        version() {
            const ret = wasm.kvstoreworld_version(this.__wbg_ptr);
            return BigInt.asUintN(64, ret);
        }
        /**
         * **THE KV-STORE VIEW-TREE** — a titled column with the version row and a `table` of
         * register rows, each `row(text(label), bind(slot), button("put"), button("del"))`. The
         * `put`/`del` buttons carry `data-turn=put/delete` and `data-arg=slot` (the register index)
         * — the SAME `{kind, props, children}` JSON the web renderer (`deos-view`) consumes.
         * @returns {string}
         */
        viewTreeJson() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.kvstoreworld_viewTreeJson(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
    }
    if (Symbol.dispose) KvStoreWorld.prototype[Symbol.dispose] = KvStoreWorld.prototype.free;
    exports.KvStoreWorld = KvStoreWorld;

    /**
     * The real `collective-choice` vote, driven from the browser tab over its own embedded
     * verified executor. One `PollWorld` owns one runtime with one poll (tally-board) cell and
     * one factory-shaped ballot cell per voter; each `cast` is a genuine cap-gated verified turn
     * (a ballot `WriteOnce(VOTE)` + a poll `Monotonic` tally bump), one-vote-per-ballot enforced
     * three depths deep, the decision-turn quorum-gated by the polis `AffineLe`.
     */
    class PollWorld {
        __destroy_into_raw() {
            const ptr = this.__wbg_ptr;
            this.__wbg_ptr = 0;
            PollWorldFinalization.unregister(this);
            return ptr;
        }
        free() {
            const ptr = this.__destroy_into_raw();
            wasm.__wbg_pollworld_free(ptr, 0);
        }
        /**
         * **Cast one vote for `option`** using the next fresh voter's ballot — a genuine
         * one-vote-per-ballot turn (each successive `cast` is a distinct ballot cell, so the
         * board grows one verified vote at a time). Returns option `option`'s re-read tally.
         * @param {number} option
         * @returns {bigint}
         */
        cast(option) {
            const ret = wasm.pollworld_cast(this.__wbg_ptr, option);
            if (ret[2]) {
                throw takeFromExternrefTable0(ret[1]);
            }
            return BigInt.asUintN(64, ret[0]);
        }
        /**
         * **Cast voter `voter`'s ballot for `option`** — the explicit-ballot cast (the shape a
         * `<dregg-poll>` uses to bind a cast to the visitor's own ballot). Re-casting the SAME
         * voter is refused by the nullifier set (the engine double-vote depth).
         * @param {number} voter
         * @param {number} option
         * @returns {bigint}
         */
        castAs(voter, option) {
            const ret = wasm.pollworld_castAs(this.__wbg_ptr, voter, option);
            if (ret[2]) {
                throw takeFromExternrefTable0(ret[1]);
            }
            return BigInt.asUintN(64, ret[0]);
        }
        /**
         * The poll cell's id (hex) — the board's sovereignty boundary, the target of tally turns.
         * @returns {string}
         */
        cellId() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.pollworld_cellId(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * **The affordance wire entry** — the web renderer fires `data-turn`/`data-arg` here.
         * `cast` casts the NEXT fresh voter's ballot for option `arg`; any other name errors.
         * @param {string} turn
         * @param {number} arg
         * @returns {bigint}
         */
        fire(turn, arg) {
            const ptr0 = passStringToWasm0(turn, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.pollworld_fire(this.__wbg_ptr, ptr0, len0, arg);
            if (ret[2]) {
                throw takeFromExternrefTable0(ret[1]);
            }
            return BigInt.asUintN(64, ret[0]);
        }
        /**
         * **THE LIGHT-CLIENT TALLY** — recompute the board from the append-only cast log ALONE
         * (never re-reading the executor's slots), as a JSON array. A verifier that never
         * re-executes replays the recorded casts and sums them; when this AGREES with
         * [`Self::tally`] the board is unforged ([`Self::verified`]).
         * @returns {string}
         */
        lightClientTally() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.pollworld_lightClientTally(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * Open a poll over `num_options` options with quorum threshold `quorum_m`, on its own
         * embedded executor. Mints the poll (tally-board) cell and installs the quorum-gated
         * program (`Monotonic` tallies + `WriteOnce(RESOLVED)` + the polis quorum `AffineLe`).
         * The operator (agent 0) signs + fee-pays every ballot / tally / resolve turn.
         * @param {number} num_options
         * @param {bigint} quorum_m
         */
        constructor(num_options, quorum_m) {
            const ret = wasm.pollworld_new(num_options, quorum_m);
            if (ret[2]) {
                throw takeFromExternrefTable0(ret[1]);
            }
            this.__wbg_ptr = ret[0];
            PollWorldFinalization.register(this, this.__wbg_ptr, this);
            return this;
        }
        /**
         * The number of active options in this poll.
         * @returns {number}
         */
        optionCount() {
            const ret = wasm.pollworld_optionCount(this.__wbg_ptr);
            return ret >>> 0;
        }
        /**
         * A witnessed read of option `option`'s running tally off the live poll cell (the
         * canonical big-endian felt lane the `Monotonic`/`AffineLe` constraints read).
         * @param {number} option
         * @returns {bigint}
         */
        read(option) {
            const ret = wasm.pollworld_read(this.__wbg_ptr, option);
            return BigInt.asUintN(64, ret);
        }
        /**
         * The committed-receipt count — the audit tape length (ballot mints + every ballot /
         * tally / resolve turn). A browser shows it to prove a cast was real, not a local poke.
         * @returns {number}
         */
        receiptCount() {
            const ret = wasm.pollworld_receiptCount(this.__wbg_ptr);
            return ret >>> 0;
        }
        /**
         * **RENDER THE LIVE TALLY TO HTML, IN-WASM** — [`Self::view_tree_json`] walked through the
         * gpui-free web renderer, each option's live `bind` painted from its `Monotonic` tally slot
         * off the committed poll cell. The `<dregg-poll>` Custom Element repaints via this after
         * each `cast`.
         * @returns {string}
         */
        renderHtml() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.pollworld_renderHtml(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * The executor's stored monotone tally as a JSON array `[c0, c1, …]` — the board a light
         * client re-derives. `nobody can stuff or forge it: each vote is a verifiable turn.
         * @returns {string}
         */
        tally() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.pollworld_tally(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * The total across all options (the running Σ TALLY the quorum gate compares to `M`).
         * @returns {bigint}
         */
        total() {
            const ret = wasm.pollworld_total(this.__wbg_ptr);
            return BigInt.asUintN(64, ret);
        }
        /**
         * **Prove the ballot's `WriteOnce(VOTE)` BITES at the EXECUTOR depth** — attempt a second,
         * value-CHANGING write to voter `voter`'s already-voted ballot directly over the verified
         * executor (bypassing the engine nullifier), which the ballot cell's `WriteOnce(VOTE)`
         * caveat must REFUSE on the commit path. Returns JSON `{refused, reason}`; `refused: true`
         * is the on-ledger one-vote-per-ballot enforcement (`collective-choice` depth (i)).
         * @param {number} voter
         * @returns {string}
         */
        tryBallotWriteOnce(voter) {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.pollworld_tryBallotWriteOnce(this.__wbg_ptr, voter);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * **Prove one-vote-per-ballot BITES at the engine depth** — attempt to re-cast voter
         * `voter`'s already-consumed ballot for `option`. Returns JSON `{refused, reason}`;
         * `refused: true` is the witnessed nullifier refusal (the consumed-ballot-proof depth).
         * @param {number} voter
         * @param {number} option
         * @returns {string}
         */
        tryDoubleVote(voter, option) {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.pollworld_tryDoubleVote(this.__wbg_ptr, voter, option);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * **Attempt the decision-turn** — set `RESOLVED := 1` on the poll cell, which the polis
         * quorum `AffineLe` (`M·RESOLVED − Σ TALLY ≤ 0`) admits ONLY once `Σ TALLY ≥ M`. Returns
         * JSON `{resolved, winner, winner_tally, total, reason}`. Below quorum the executor
         * refuses the turn (`resolved: false`); at/above quorum it commits. Idempotent once resolved.
         * @returns {string}
         */
        tryResolve() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.pollworld_tryResolve(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * **THE SELF-VERIFY** — `true` iff the executor's stored monotone tally EQUALS the
         * light-client recompute from the cast log (the anti-stuffing check, in the tab).
         * @returns {boolean}
         */
        verified() {
            const ret = wasm.pollworld_verified(this.__wbg_ptr);
            return ret !== 0;
        }
        /**
         * **THE POLL VIEW-TREE** — a titled column over a `table` of option rows, each
         * `row(text(label), bind(tally slot))`. The SAME `{kind, props, children}` JSON the web
         * renderer (`deos-view::parse_view_tree`) consumes — serve it and the live board paints.
         * @returns {string}
         */
        viewTreeJson() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.pollworld_viewTreeJson(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
    }
    if (Symbol.dispose) PollWorld.prototype[Symbol.dispose] = PollWorld.prototype.free;
    exports.PollWorld = PollWorld;

    /**
     * The tally-board card, driven from the browser tab over its own embedded verified executor.
     * One `TallyWorld` owns one runtime with one tally-cell (agent 0); each tally is a model slot
     * and each `+1`/`-1` click fires a REAL cap-gated verified turn — the wasm realization of a
     * multi-row, multi-affordance deos-js card over the full `Row`/`Table` ViewNode vocabulary.
     */
    class TallyWorld {
        __destroy_into_raw() {
            const ptr = this.__wbg_ptr;
            this.__wbg_ptr = 0;
            TallyWorldFinalization.unregister(this);
            return ptr;
        }
        free() {
            const ptr = this.__destroy_into_raw();
            wasm.__wbg_tallyworld_free(ptr, 0);
        }
        /**
         * The tally-cell's id (hex) — the sovereignty boundary, the agent of its turns.
         * @returns {string}
         */
        cellId() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.tallyworld_cellId(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * **Move one tally** — commit ONE cap-gated verified turn: the tally `arg` advances or
         * retreats by one (`turn` = `"inc"`/`"dec"`), then return the re-read value (the new
         * `bind` value the browser re-paints). `arg` is the SLOT index the button carried as
         * `data-arg`. A `dec` saturates at 0; an unknown direction or out-of-range slot commits
         * nothing and errors (the native `FireError::Unknown`).
         * @param {string} turn
         * @param {number} arg
         * @returns {bigint}
         */
        fire(turn, arg) {
            const ptr0 = passStringToWasm0(turn, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.tallyworld_fire(this.__wbg_ptr, ptr0, len0, arg);
            if (ret[2]) {
                throw takeFromExternrefTable0(ret[1]);
            }
            return BigInt.asUintN(64, ret[0]);
        }
        /**
         * Mint a fresh tally board on its own embedded executor, seeding each tally slot. The
         * tally-cell is agent 0 (single-custody, `AuthRequired::None` holder — the posture
         * `Applet::mint` gives a card), funded so a metered turn has a source. `seeds[i]` seeds
         * tally `i` (defaults to a clearly-distinct `[3, 1, 4]`); each non-zero seed is committed
         * via a REAL verified turn, so the genesis board itself leaves receipts.
         * @param {BigUint64Array} seeds
         */
        constructor(seeds) {
            const ptr0 = passArray64ToWasm0(seeds, wasm.__wbindgen_malloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.tallyworld_new(ptr0, len0);
            if (ret[2]) {
                throw takeFromExternrefTable0(ret[1]);
            }
            this.__wbg_ptr = ret[0];
            TallyWorldFinalization.register(this, this.__wbg_ptr, this);
            return this;
        }
        /**
         * A witnessed read of tally `slot` off the live ledger — the value the web renderer
         * paints into the matching `data-slot` span (the SAME read each row's `bind` makes).
         * @param {number} slot
         * @returns {bigint}
         */
        read(slot) {
            const ret = wasm.tallyworld_read(this.__wbg_ptr, slot);
            return BigInt.asUintN(64, ret);
        }
        /**
         * The committed-receipt count — the audit tape length (one per fired turn, plus the
         * genesis seeds). A browser shows it to prove a `+1`/`-1` was a real turn, not a poke.
         * @returns {number}
         */
        receiptCount() {
            const ret = wasm.tallyworld_receiptCount(this.__wbg_ptr);
            return ret >>> 0;
        }
        /**
         * **RENDER THE TALLY BOARD TO HTML, IN-WASM** — [`Self::view_tree_json`] (a `Table` of
         * `Row`s) walked through the gpui-free web renderer, each row's live `bind` painted from
         * its own tally slot off the committed ledger ([`Self::read`]). The Custom Element repaints
         * via this after each `+1`/`−1` fire.
         * @returns {string}
         */
        renderHtml() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.tallyworld_renderHtml(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
        /**
         * **THE TALLY VIEW-TREE** — a `table` of `row`s, one per named tally: each row carries a
         * `text` label, a live `bind` of that tally's slot, and `+1`/`-1` affordance `button`s.
         * The SAME `{kind, props, children}` JSON the web renderer (`deos-view::parse_view_tree`)
         * consumes — serve it and the board paints live in a browser.
         * @returns {string}
         */
        viewTreeJson() {
            let deferred1_0;
            let deferred1_1;
            try {
                const ret = wasm.tallyworld_viewTreeJson(this.__wbg_ptr);
                deferred1_0 = ret[0];
                deferred1_1 = ret[1];
                return getStringFromWasm0(ret[0], ret[1]);
            } finally {
                wasm.__wbindgen_free(deferred1_0, deferred1_1, 1);
            }
        }
    }
    if (Symbol.dispose) TallyWorld.prototype[Symbol.dispose] = TallyWorld.prototype.free;
    exports.TallyWorld = TallyWorld;

    /**
     * Advance the block height for timeout simulation.
     * @param {number} handle
     * @param {bigint} blocks
     * @returns {any}
     */
    function advance_height(handle, blocks) {
        const ret = wasm.advance_height(handle, blocks);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.advance_height = advance_height;

    /**
     * Attenuate an existing held token by narrowing its actions/resource.
     * @param {number} handle
     * @param {number} agent_index
     * @param {number} token_index
     * @param {string} restrict_actions_json
     * @param {string} restrict_resource
     * @returns {any}
     */
    function agent_attenuate(handle, agent_index, token_index, restrict_actions_json, restrict_resource) {
        const ptr0 = passStringToWasm0(restrict_actions_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(restrict_resource, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.agent_attenuate(handle, agent_index, token_index, ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.agent_attenuate = agent_attenuate;

    /**
     * Mint a token for an agent (for intent matching).
     * `actions_json` is a JSON array of strings like `["read", "write"]`.
     * @param {number} handle
     * @param {number} agent_index
     * @param {string} resource
     * @param {string} actions_json
     * @param {bigint} expiry
     * @returns {any}
     */
    function agent_mint_token(handle, agent_index, resource, actions_json, expiry) {
        const ptr0 = passStringToWasm0(resource, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(actions_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.agent_mint_token(handle, agent_index, ptr0, len0, ptr1, len1, expiry);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.agent_mint_token = agent_mint_token;

    /**
     * Assemble the canonical `SignedTurn` submission envelope — the exact bytes the
     * node's `POST /api/turns/submit-signed` decodes with
     * `postcard::from_bytes::<dregg_sdk::SignedTurn>` — from an encoded `Turn` and a
     * 32-byte Ed25519 seed.
     *
     * This routes envelope assembly through the SDK's canonical
     * [`AgentCipherclerk::sign_turn`] instead of the extension hand-rolling the
     * postcard layout in JS. That matters now that the envelope is **HYBRID**: the
     * SDK signs the canonical `Turn::hash` (v3) with BOTH the Ed25519 identity AND
     * the ML-DSA-65 (FIPS 204) key derived deterministically from the same seed
     * (`dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed`, ctx `b"dregg-hybrid-turn-v1"`),
     * and the resulting `SignedTurn` carries the trailing `pq_signature` / `pq_signer`
     * fields. Hand-encoding those two variable-length halves (a 3309-byte ML-DSA
     * signature + a 1952-byte public key, each behind a postcard varint) in JS is
     * exactly the postcard-layout coupling this removes: the client emits the PQ half
     * end-to-end, and the wire shape stays owned by the SDK's own serializer.
     *
     * The classical half is unchanged — the node still re-derives `turn.hash()` and
     * verifies the Ed25519 signature; the PQ half is verified over the SAME hash when
     * present (fail-closed) and only *required* once the node flips `require_pq`.
     *
     * Arguments:
     * - `turn_bytes`: the signed, encoded `Turn` (postcard or self-describing JSON —
     *   tried in that order, matching [`sign_turn_v3`]'s encoding contract). Pass the
     *   `turn_bytes_json` that `sign_turn_v3` emits for a guaranteed round-trip.
     * - `sender_privkey`: the 32-byte Ed25519 seed (the cipherclerk's secret key).
     *
     * Returns a `Uint8Array` of the postcard-encoded `SignedTurn` ready to POST.
     * @param {Uint8Array} turn_bytes
     * @param {Uint8Array} sender_privkey
     * @returns {Uint8Array}
     */
    function assemble_signed_turn_envelope(turn_bytes, sender_privkey) {
        const ptr0 = passArray8ToWasm0(turn_bytes, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(sender_privkey, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.assemble_signed_turn_envelope(ptr0, len0, ptr1, len1);
        if (ret[3]) {
            throw takeFromExternrefTable0(ret[2]);
        }
        var v3 = getArrayU8FromWasm0(ret[0], ret[1]).slice();
        wasm.__wbindgen_free(ret[0], ret[1] * 1, 1);
        return v3;
    }
    exports.assemble_signed_turn_envelope = assemble_signed_turn_envelope;

    /**
     * Attempt time-travel rewind on the sim runtime (STARBRIDGE-FOLLOWUP-03
     * on blocked §5.10 + Q4).
     *
     * For target <= current: returns Ok(()) only for exact current (no-op) or
     * Err explaining the pending snapshot format dependency.
     * For target > current: explicit forward-only error.
     *
     * Provides the JS-callable surface + error shape for `<dregg-...>`
     * scrubber / cursor UI to target. `caps.timeTravel` should stay false
     * in surfaces until real impl lands. See runtime.rs docs and plan §5.10.
     *
     * Thin + safe (no proving stack, delegates to stub).
     * @param {number} handle
     * @param {bigint} target_height
     * @returns {any}
     */
    function attempt_time_travel(handle, target_height) {
        const ret = wasm.attempt_time_travel(handle, target_height);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.attempt_time_travel = attempt_time_travel;

    /**
     * Attenuate a macaroon token with service/action restrictions.
     *
     * `actions` is a comma-separated list of action strings (e.g. "read,write").
     * `expires_secs` is seconds from now (0 means no expiry caveat).
     *
     * Returns JSON: { "token": "<em2_...>", "caveats_added": N }
     * @param {string} token_str
     * @param {Uint8Array} root_key
     * @param {string} service
     * @param {string} actions
     * @param {bigint} expires_secs
     * @returns {any}
     */
    function attenuate_token(token_str, root_key, service, actions, expires_secs) {
        const ptr0 = passStringToWasm0(token_str, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(root_key, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(service, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ptr3 = passStringToWasm0(actions, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len3 = WASM_VECTOR_LEN;
        const ret = wasm.attenuate_token(ptr0, len0, ptr1, len1, ptr2, len2, ptr3, len3, expires_secs);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.attenuate_token = attenuate_token;

    /**
     * Compute a BLAKE3 hash of an arbitrary string, returning the hex digest.
     *
     * This is exposed so the extension can produce BLAKE3 hashes without pulling
     * in a full JS implementation.
     * @param {string} input
     * @returns {string}
     */
    function blake3_hash(input) {
        let deferred2_0;
        let deferred2_1;
        try {
            const ptr0 = passStringToWasm0(input, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.blake3_hash(ptr0, len0);
            deferred2_0 = ret[0];
            deferred2_1 = ret[1];
            return getStringFromWasm0(ret[0], ret[1]);
        } finally {
            wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
        }
    }
    exports.blake3_hash = blake3_hash;

    /**
     * Build a committed (private) transfer turn.
     *
     * Takes a JSON params object and returns the turn bytes + turn_id.
     * @param {string} params_json
     * @returns {any}
     */
    function build_committed_turn(params_json) {
        const ptr0 = passStringToWasm0(params_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.build_committed_turn(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.build_committed_turn = build_committed_turn;

    /**
     * Build a faceted capability mask.
     *
     * `allowed_effects_json`: JSON array of effect names to permit.
     * Valid names: "set_field", "transfer", "grant_capability", "revoke_capability",
     *             "emit_event", "increment_nonce", "create_cell", "set_permissions",
     *             "set_verification_key"
     *
     * Returns JSON: { mask: u32, description: string[] }
     * @param {string} allowed_effects_json
     * @returns {any}
     */
    function build_facet_mask(allowed_effects_json) {
        const ptr0 = passStringToWasm0(allowed_effects_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.build_facet_mask(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.build_facet_mask = build_facet_mask;

    /**
     * Build and sign a canonical turn from a JSON spec, using `AgentCipherclerk` as
     * the canonical signing path.
     *
     * The cipherclerk is constructed from `sender_privkey` (32-byte Ed25519 seed
     * carried by the extension background) using `AgentCipherclerk::from_key_bytes`,
     * and the turn is built via `AgentCipherclerk::make_action` + `AgentCipherclerk::make_turn_for`.
     * The action records one `Effect::IncrementNonce` (a no-op state advancement)
     * with a custom `method` field derived from `turnSpec.action` — it carries the
     * semantic intent without requiring ledger state for the extension's broadcast path.
     *
     * JSON input:
     * ```json
     * {
     *   "sender_pubkey": [32 bytes as number[]],
     *   "sender_privkey": [32 bytes as number[]],
     *   "action": "transfer",
     *   "resource": "docs/*",
     *   "amount": 0,
     *   "recipient": null,
     *   "metadata": null,
     *   "timestamp": 1716000000
     * }
     * ```
     *
     * Returns JSON: `{ "turn_id": "<hex>", "turn_bytes": <Uint8Array> }`.
     * `turn_bytes` is the postcard-serialized `Turn` that the node's
     * `/turns/submit` endpoint expects.
     * @param {string} spec_json
     * @returns {any}
     */
    function build_turn(spec_json) {
        const ptr0 = passStringToWasm0(spec_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.build_turn(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.build_turn = build_turn;

    /**
     * Check if a stealth announcement is addressed to us.
     *
     * Performs the DH check: shared = X25519(view_privkey, ephemeral_pubkey),
     * then derives expected one-time pubkey and compares.
     *
     * Returns JSON: { is_ours: bool, one_time_privkey: Vec<u8> | null }
     * @param {Uint8Array} view_privkey
     * @param {Uint8Array} spend_pubkey
     * @param {Uint8Array} ephemeral_pubkey
     * @param {Uint8Array} one_time_pubkey
     * @returns {any}
     */
    function check_stealth_ownership(view_privkey, spend_pubkey, ephemeral_pubkey, one_time_pubkey) {
        const ptr0 = passArray8ToWasm0(view_privkey, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(spend_pubkey, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passArray8ToWasm0(ephemeral_pubkey, wasm.__wbindgen_malloc);
        const len2 = WASM_VECTOR_LEN;
        const ptr3 = passArray8ToWasm0(one_time_pubkey, wasm.__wbindgen_malloc);
        const len3 = WASM_VECTOR_LEN;
        const ret = wasm.check_stealth_ownership(ptr0, len0, ptr1, len1, ptr2, len2, ptr3, len3);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.check_stealth_ownership = check_stealth_ownership;

    /**
     * Build and sign a canonical `Effect::CreateCellFromFactory` turn from a
     * JSON spec, using `AgentCipherclerk::create_from_factory` as the canonical
     * constructor-transparency path.
     *
     * This replaces the standalone `create_from_factory` derivation function
     * for the extension's `window.dregg.createFromFactory` path. The previous
     * shape only computed `(child_vk, param_hash)` deterministically — useful
     * for client-side preview, but it never actually minted a cell. The
     * canonical path is: build a real signed turn, submit it via
     * `/turns/submit`, and let the node's `TurnExecutor` mint the cell with
     * real provenance tracking.
     *
     * JSON input:
     * ```json
     * {
     *   "sender_privkey": [32 bytes as number[]],
     *   "factory_vk_hex": "<64 hex chars>",
     *   "owner_pubkey_hex": "<64 hex chars>",
     *   "token_id_hex": "<64 hex chars>",
     *   "mode": "Hosted" | "Sovereign",
     *   "program_vk_hex": "<optional 64 hex chars>",
     *   "initial_fields": [[field_index, value], ...],
     *   "initial_balance": 0
     * }
     * ```
     *
     * Returns JSON: `{ "turn_id": "<hex>", "turn_bytes": <Uint8Array>,
     * "child_vk": "<hex>", "param_hash": "<hex>", "factory_vk": "<hex>" }`.
     *
     * `turn_bytes` is the postcard-serialized `Turn` that the node's
     * `/turns/submit` endpoint accepts. `child_vk` / `param_hash` are
     * surfaced so the caller can immediately compute the new cell's identity
     * without round-tripping through the node.
     * @param {string} spec_json
     * @returns {any}
     */
    function cipherclerk_create_from_factory(spec_json) {
        const ptr0 = passStringToWasm0(spec_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.cipherclerk_create_from_factory(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.cipherclerk_create_from_factory = cipherclerk_create_from_factory;

    /**
     * Build a cipherclerk-signed [`Turn`] carrying a single named action.
     *
     * Routes through `AgentCipherclerk::make_action(target, method, effects,
     * federation_id)` + `AgentCipherclerk::make_turn_for(domain, action)` so
     * the action's `authorization` field is a real Ed25519 signature
     * over the canonical action bytes, bound to the federation_id.
     *
     * The action's `method` carries the semantic name
     * (e.g. `"propose_routes"`, `"vote_on_proposal"`); the request payload
     * is carried in the [`Turn::memo`] field as a JSON string. The
     * federation can dispatch by `method` and decode the memo to recover
     * the proposal / vote payload. The action's effects are a single
     * `IncrementNonce` (no ledger mutation in the action itself — the
     * federation drives any state change from the memo'd payload).
     *
     * JSON input:
     * ```json
     * {
     *   "sender_privkey": [32 bytes],
     *   "method": "propose_routes",
     *   "memo_json": "<arbitrary JSON string for the action body>",
     *   "federation_id_hex": "<optional 64 hex chars>"
     * }
     * ```
     *
     * Returns JSON: `{ turn_id, turn_bytes, agent_cell_id, method }`.
     * `turn_bytes` is the postcard-serialized signed `Turn` for the node's
     * `/turns/submit` endpoint.
     * @param {string} spec_json
     * @returns {any}
     */
    function cipherclerk_make_action_turn(spec_json) {
        const ptr0 = passStringToWasm0(spec_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.cipherclerk_make_action_turn(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.cipherclerk_make_action_turn = cipherclerk_make_action_turn;

    /**
     * Build a peer-exchange `PeerStateTransition` signed by the cipherclerk's
     * Ed25519 key via `AgentCipherclerk::peer_exchange(domain)`. This replaces
     * the prior `peer_exchange_with_proof` shape (which only emitted
     * canonical-looking hex blobs but did not sign with the cipherclerk).
     *
     * The transition carries:
     *   - `cell_id`        = `cclerk.cell_id("default")`
     *   - `old_commitment` = blake3-derived from (sender, receiver)
     *   - `new_commitment` = blake3-derived from (old, amount, receiver)
     *   - `effects_hash`   = blake3 of postcard(`Effect::Transfer{..}`)
     *   - `sequence`       = 1 (each call constructs a fresh PeerExchange
     *                          session — wasm has no persistent session)
     *   - `timestamp`      = caller-supplied (wasm has no `SystemTime::now()`)
     *   - `signature`      = Ed25519 over the canonical message
     *
     * JSON input:
     * ```json
     * {
     *   "sender_privkey": [32 bytes as number[]],
     *   "receiver_cell_hex": "<64 hex>",
     *   "amount": <u64>,
     *   "timestamp": <i64 unix-seconds>
     * }
     * ```
     *
     * Returns JSON: `{ exchange_id, proof_commitment, sender_cell,
     * receiver_cell, transition_bytes, amount }`. `transition_bytes` is
     * the postcard-encoded `PeerStateTransition` — the wire format peers
     * exchange directly. `exchange_id` / `proof_commitment` are retained
     * for shape compatibility with the legacy binding so existing
     * page-side callers don't break.
     * @param {string} spec_json
     * @returns {any}
     */
    function cipherclerk_peer_exchange(spec_json) {
        const ptr0 = passStringToWasm0(spec_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.cipherclerk_peer_exchange(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.cipherclerk_peer_exchange = cipherclerk_peer_exchange;

    /**
     * Build an `EncryptedIntent` via the canonical SDK path
     * (`AgentCipherclerk::post_encrypted_intent`). The cipherclerk's Ed25519 identity
     * is the source of the `commitment_id` field; the intent body is sealed
     * with a fresh ephemeral keypair (per `EncryptedIntent::create`).
     *
     * JSON input:
     * ```json
     * {
     *   "sender_privkey": [32 bytes as number[]],
     *   "match_spec": { ... canonical MatchSpec JSON ... },
     *   "kind": "Need" | "Offer" | "Query",
     *   "expiry": null | <unix-seconds>
     * }
     * ```
     *
     * `match_spec` is parsed via the canonical `dregg_intent::MatchSpec`
     * serde shape, so the field names are exactly those of the Rust type.
     * The extension already coerces its inbound MatchSpec to this shape
     * for `dregg:postIntent` / `compute_intent_id`, so the same payload
     * flows through here.
     *
     * Returns JSON: `{ intent_id: <hex>, encrypted_intent_bytes: Uint8Array,
     * expiry: u64|null }`. `encrypted_intent_bytes` is the postcard-serialized
     * `EncryptedIntent`, ready for gossip propagation or for the extension
     * to forward to `/intents/encrypted` (or equivalent transport).
     * @param {string} spec_json
     * @returns {any}
     */
    function cipherclerk_post_encrypted_intent(spec_json) {
        const ptr0 = passStringToWasm0(spec_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.cipherclerk_post_encrypted_intent(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.cipherclerk_post_encrypted_intent = cipherclerk_post_encrypted_intent;

    /**
     * Build a private-transfer turn via the canonical SDK path
     * (`AgentCipherclerk::private_transfer`). The turn carries a Pedersen value
     * commitment (amount hidden) addressed to a freshly-derived stealth
     * one-time pubkey for the recipient meta-address.
     *
     * JSON input:
     * ```json
     * {
     *   "sender_privkey": [32 bytes as number[]],
     *   "amount": <u64>,
     *   "asset_type": <u64>,
     *   "recipient_meta": {
     *     "spend_pubkey": [32 bytes as number[]],
     *     "view_pubkey":  [32 bytes as number[]]
     *   }
     * }
     * ```
     *
     * Returns JSON: `{ turn_id: <hex>, turn_bytes: Uint8Array,
     * agent_cell_id: <hex> }`. `turn_bytes` is the postcard-serialized
     * `Turn` ready for `/turns/submit`.
     * @param {string} spec_json
     * @returns {any}
     */
    function cipherclerk_private_transfer(spec_json) {
        const ptr0 = passStringToWasm0(spec_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.cipherclerk_private_transfer(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.cipherclerk_private_transfer = cipherclerk_private_transfer;

    /**
     * DFA compile/eval stub. In full: delegates to dregg_dfa::compiler + air.
     * For inspector <dregg-dfa> + relay/pubsub. Returns placeholder shape today.
     * @param {string} _pattern_json
     * @returns {any}
     */
    function compile_dfa(_pattern_json) {
        const ptr0 = passStringToWasm0(_pattern_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.compile_dfa(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.compile_dfa = compile_dfa;

    /**
     * Verify each input proof for real, then return the boolean composition of
     * the per-proof verdicts under `mode`.
     *
     * This is the honest counterpart to [`compose_proofs`]: where that function
     * only content-addresses the inputs (and so always reports `valid: false`),
     * this one actually discharges each proof against its canonical verifier and
     * reports a `valid` that is the genuine conjunction / disjunction of REAL
     * verifications — no BLAKE3 stand-in.
     *
     * `proofs_json` is a JSON array of tagged verification envelopes. Each entry
     * carries a `kind` plus exactly the inputs that kind's verifier needs:
     *
     * ```json
     * [
     *   { "kind": "membership",   "proof_json": "<Ir2ProofEnvelope JSON>" },
     *   { "kind": "range",        "commitment_hex": "<64-hex>", "range_proof_hex": "<hex>" },
     *   { "kind": "conservation", "input_commitments": ["<64-hex>", ...],
     *                             "output_commitments": ["<64-hex>", ...],
     *                             "proof": { "excess_commitment": "...",
     *                                        "nonce_commitment": "...",
     *                                        "response": "..." },
     *                             "message_hex": "<hex>",
     *                             "output_range_proofs": ["<hex>", ...] }
     * ]
     * ```
     *
     * `mode`:
     * - `"and"` — the composition holds iff EVERY proof verifies (the default
     *   conjunction `O(1)`-verification target).
     * - `"or"` — holds iff at least ONE proof verifies.
     * - `"chain"` — sequential: holds iff every proof verifies (and the per-proof
     *   results report the first break point).
     * - `"aggregate"` — batch: same verdict as `"and"`, framed as one pass.
     *
     * Returns JSON:
     * ```json
     * { "composed_proof": "<hex content id>", "mode": "and",
     *   "input_count": 3, "valid": true,
     *   "results": [ { "kind": "range", "valid": true, "error": null }, ... ] }
     * ```
     * @param {string} proofs_json
     * @param {string} mode
     * @returns {any}
     */
    function compose_and_verify_proofs(proofs_json, mode) {
        const ptr0 = passStringToWasm0(proofs_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(mode, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.compose_and_verify_proofs(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.compose_and_verify_proofs = compose_and_verify_proofs;

    /**
     * Compose multiple proofs using AND/OR/Chain/Aggregate strategies.
     *
     * `proofs_json`: JSON array of proof objects { proof_json, public_inputs }
     * `mode`: "and" | "or" | "chain" | "aggregate"
     *
     * Returns JSON: { composed_proof, mode, input_count, valid }
     * @param {string} proofs_json
     * @param {string} mode
     * @returns {any}
     */
    function compose_proofs(proofs_json, mode) {
        const ptr0 = passStringToWasm0(proofs_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(mode, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.compose_proofs(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.compose_proofs = compose_proofs;

    /**
     * Compute a canonical intent ID exactly as the Rust intent engine does.
     *
     * Takes a JSON object with: kind, actions, resource_pattern, constraints, expiry, creator.
     * Returns the hex-encoded 32-byte BLAKE3 intent ID using postcard serialization,
     * identical to `Intent::compute_id()` in the `dregg-intent` crate.
     *
     * JSON schema:
     * ```json
     * {
     *   "kind": "Need" | "Offer" | "Query",
     *   "actions": [{"action": "read", "resource": "docs/*"}, ...],
     *   "constraints": [{"AppId": "x"}, {"Service": "y"}, ...],
     *   "min_budget": null | 1000,
     *   "resource_pattern": null | "docs/*",
     *   "compound": null | [{ "actions": [...], ... }],
     *   "expiry": 1716000000,
     *   "creator": [170, 170, ...] (32 bytes),
     *   "stake_commitment": null | [1, 2, 3, ...] (32 bytes)
     * }
     * ```
     * @param {string} intent_json
     * @returns {string}
     */
    function compute_intent_id(intent_json) {
        let deferred3_0;
        let deferred3_1;
        try {
            const ptr0 = passStringToWasm0(intent_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.compute_intent_id(ptr0, len0);
            var ptr2 = ret[0];
            var len2 = ret[1];
            if (ret[3]) {
                ptr2 = 0; len2 = 0;
                throw takeFromExternrefTable0(ret[2]);
            }
            deferred3_0 = ptr2;
            deferred3_1 = len2;
            return getStringFromWasm0(ptr2, len2);
        } finally {
            wasm.__wbindgen_free(deferred3_0, deferred3_1, 1);
        }
    }
    exports.compute_intent_id = compute_intent_id;

    /**
     * Compute a Merkle root from a list of leaf strings.
     *
     * Returns JSON: { "root_hex": "...", "num_leaves": N, "tree_depth": D }
     * @param {string} leaves_json
     * @returns {any}
     */
    function compute_merkle_root(leaves_json) {
        const ptr0 = passStringToWasm0(leaves_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.compute_merkle_root(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.compute_merkle_root = compute_merkle_root;

    /**
     * Create an agent (cipherclerk + cell) in the runtime.
     * Returns the agent index (handle).
     *
     * Genesis (agent 0) is birth-by-fiat: the ledger inserts the root cell
     * directly because no signer exists yet. Subsequent agents are minted
     * via `Effect::CreateCellFromFactory` against the runtime's default
     * test-cipherclerk factory — the canonical constructor-transparency path.
     * To mint from a specific factory, use
     * [`create_agent_with_factory`] / [`deploy_factory_descriptor`].
     * @param {number} handle
     * @param {string} name
     * @param {bigint} initial_balance
     * @returns {any}
     */
    function create_agent(handle, name, initial_balance) {
        const ptr0 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.create_agent(handle, ptr0, len0, initial_balance);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_agent = create_agent;

    /**
     * Create an agent whose cell is minted from a specific factory VK
     * (instead of the runtime's default test-cipherclerk factory).
     *
     * The factory must have been deployed via
     * [`deploy_factory_descriptor`]. The new cell carries a `Provenance`
     * record pointing at this factory, so a downstream `verify_provenance`
     * against the named factory set will return true.
     *
     * Genesis (the first agent in the runtime) cannot be born from a
     * factory — no signer exists yet. This binding always returns an error
     * for agent index 0; create the genesis agent via [`create_agent`]
     * first, then mint subsequent agents from your factory.
     * @param {number} handle
     * @param {string} name
     * @param {bigint} initial_balance
     * @param {string} factory_vk_hex
     * @returns {any}
     */
    function create_agent_with_factory(handle, name, initial_balance, factory_vk_hex) {
        const ptr0 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(factory_vk_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.create_agent_with_factory(handle, ptr0, len0, initial_balance, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_agent_with_factory = create_agent_with_factory;

    /**
     * Create a bearer capability proof.
     *
     * P1 audit fix: the previous version produced
     * `BLAKE3("dregg-bearer-cap-v1", delegator_pubkey || target || action || expiry)`,
     * which used **public** material only — anyone could forge a "bearer token"
     * by recomputing the same hash. This was not a bearer capability; it was a
     * content-addressable label.
     *
     * The new bearer cap is an Ed25519 signature by the delegator over a binding
     * hash over `(delegator_pubkey, target_cell, action, expiry)`. Only the
     * delegator can issue (they hold the signing key); anyone with the delegator
     * pubkey can verify.
     *
     * `delegator_signing_key_hex`: 32-byte Ed25519 secret seed (held in
     *   `Zeroizing`; do not pass material you don't control).
     * `target_cell_hex`: 32-byte hex ID of the cell being targeted.
     * `action_name`: the action to authorize (e.g., "transfer", "read").
     * `expiry`: Unix timestamp after which the cap expires (0 = no expiry).
     *
     * Returns JSON: `{ bearer_token_hex (64-byte Ed25519 sig), delegator_pubkey_hex,
     * binding_hex, target_cell, action, expiry }`
     * @param {string} delegator_signing_key_hex
     * @param {string} target_cell_hex
     * @param {string} action_name
     * @param {bigint} expiry
     * @returns {any}
     */
    function create_bearer_cap(delegator_signing_key_hex, target_cell_hex, action_name, expiry) {
        const ptr0 = passStringToWasm0(delegator_signing_key_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(target_cell_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(action_name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ret = wasm.create_bearer_cap(ptr0, len0, ptr1, len1, ptr2, len2, expiry);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_bearer_cap = create_bearer_cap;

    /**
     * Create a *real* `BearerCapProof` (SignedDelegation variant) usable in
     * canonical turns / `Authorization::Bearer`.
     *
     * Extended (FOLLOWUP-14 inspector cluster): supports optional revocation_channel
     * and allowed_effects facet mask for full capability model integration with
     * <dregg-revocation-channel> and facet attenuation. Empty rev hex or mask=0 means absent.
     *
     * Returns JSON-serialized BearerCapProof (matches the shape already
     * surfaced in AuthorizationView and TurnReceipt actions).
     * @param {string} delegator_signing_key_hex
     * @param {string} target_cell_hex
     * @param {string} permissions
     * @param {string} bearer_pubkey_hex
     * @param {bigint} expires_at
     * @param {string} federation_id_hex
     * @param {string} revocation_channel_hex
     * @param {number} allowed_effects_mask
     * @returns {any}
     */
    function create_bearer_cap_proof(delegator_signing_key_hex, target_cell_hex, permissions, bearer_pubkey_hex, expires_at, federation_id_hex, revocation_channel_hex, allowed_effects_mask) {
        const ptr0 = passStringToWasm0(delegator_signing_key_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(target_cell_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(permissions, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ptr3 = passStringToWasm0(bearer_pubkey_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len3 = WASM_VECTOR_LEN;
        const ptr4 = passStringToWasm0(federation_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len4 = WASM_VECTOR_LEN;
        const ptr5 = passStringToWasm0(revocation_channel_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len5 = WASM_VECTOR_LEN;
        const ret = wasm.create_bearer_cap_proof(ptr0, len0, ptr1, len1, ptr2, len2, ptr3, len3, expires_at, ptr4, len4, ptr5, len5, allowed_effects_mask);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_bearer_cap_proof = create_bearer_cap_proof;

    /**
     * Build a canonical `Authorization::CapTpDelivered` envelope, postcard-encode
     * it, and return the bytes.
     *
     * This is the substrate behind the extension's
     * `dregg.createCapTpDeliveredAuth(...)` surface (STARBRIDGE-PLAN §4.3 Task #28
     * item 7). A starbridge-app performing a three-party CapTP handoff (Alice→Bob→Carol)
     * builds the recipient-side authorization client-side from:
     * - `handoff_cert_b58`: the introducer-signed `HandoffCertificate` as either the
     *   compact `dregg-handoff:<base58>` string or a bare base58 of its postcard bytes.
     * - `introducer_pk_hex`: 32-byte introducer public key (verifies
     *   `handoff_cert.introducer_signature`).
     * - `sender_pk_hex`: 32-byte recipient/sender public key (must equal
     *   `handoff_cert.recipient_pk`).
     * - `sender_sig_hex`: 64-byte Ed25519 signature by `sender_pk` over the
     *   `captp_delivered_signing_message`.
     *
     * The signature itself is produced upstream (by the recipient's cipherclerk over
     * `Authorization::captp_delivered_signing_message[_for_federation]`); this
     * constructor only assembles the canonical variant and serializes it. The
     * executor's `verify_captp_delivered` performs the real verification at apply time.
     *
     * Returns JSON: `{ "auth_bytes": <Uint8Array>, "recipient_pk": "<hex>",
     * "introducer_federation": "<hex>" }`.
     * @param {string} handoff_cert_b58
     * @param {string} introducer_pk_hex
     * @param {string} sender_pk_hex
     * @param {string} sender_sig_hex
     * @returns {any}
     */
    function create_captp_delivered_auth(handoff_cert_b58, introducer_pk_hex, sender_pk_hex, sender_sig_hex) {
        const ptr0 = passStringToWasm0(handoff_cert_b58, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(introducer_pk_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(sender_pk_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ptr3 = passStringToWasm0(sender_sig_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len3 = WASM_VECTOR_LEN;
        const ret = wasm.create_captp_delivered_auth(ptr0, len0, ptr1, len1, ptr2, len2, ptr3, len3);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_captp_delivered_auth = create_captp_delivered_auth;

    /**
     * Create a cell in the runtime via a real `Effect::CreateCell` turn issued
     * by the genesis agent (agent 0). Requires at least one agent to exist as
     * the signer — if there are none, returns an error.
     *
     * `owner_pk` is a 32-byte public key (hex string).
     * Returns JSON with the cell_id.
     * @param {number} handle
     * @param {string} owner_pk_hex
     * @param {bigint} initial_balance
     * @returns {any}
     */
    function create_cell(handle, owner_pk_hex, initial_balance) {
        const ptr0 = passStringToWasm0(owner_pk_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.create_cell(handle, ptr0, len0, initial_balance);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_cell = create_cell;

    /**
     * Create a federation with `num_nodes` real federation nodes. Each node has
     * a freshly generated Ed25519 keypair and an empty `RevocationTree`. The
     * federation index is its handle for subsequent calls.
     * @param {number} handle
     * @param {string} name
     * @param {number} num_nodes
     * @returns {any}
     */
    function create_federation(handle, name, num_nodes) {
        const ptr0 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.create_federation(handle, ptr0, len0, num_nodes);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_federation = create_federation;

    /**
     * Create a cell from a factory descriptor.
     *
     * Validates the creation parameters against the factory constraints and
     * returns the derived child cell VK hash.
     *
     * `factory_descriptor_json`: JSON representation of the factory descriptor
     * `params_json`: JSON of creation parameters (initial_balance, field_inits)
     *
     * Returns JSON: { child_vk, param_hash, factory_vk }
     * @param {string} factory_vk_hex
     * @param {string} owner_pubkey_hex
     * @param {bigint} _initial_balance
     * @returns {any}
     */
    function create_from_factory(factory_vk_hex, owner_pubkey_hex, _initial_balance) {
        const ptr0 = passStringToWasm0(factory_vk_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(owner_pubkey_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.create_from_factory(ptr0, len0, ptr1, len1, _initial_balance);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_from_factory = create_from_factory;

    /**
     * Create an intent.
     *
     * `kind`: "Need", "Offer", or "Query"
     * `actions_json`: `[{"action": "read", "resource": "docs/*"}, ...]`
     * `constraints_json`: `[{"AppId": "x"}, {"Service": "y"}, ...]`
     * @param {number} handle
     * @param {number} agent_index
     * @param {string} kind
     * @param {string} actions_json
     * @param {string} constraints_json
     * @param {string} resource_pattern
     * @param {bigint} expiry
     * @returns {any}
     */
    function create_intent(handle, agent_index, kind, actions_json, constraints_json, resource_pattern, expiry) {
        const ptr0 = passStringToWasm0(kind, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(actions_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(constraints_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ptr3 = passStringToWasm0(resource_pattern, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len3 = WASM_VECTOR_LEN;
        const ret = wasm.create_intent(handle, agent_index, ptr0, len0, ptr1, len1, ptr2, len2, ptr3, len3, expiry);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_intent = create_intent;

    /**
     * Create a note commitment for an agent.
     * @param {number} handle
     * @param {number} agent_index
     * @param {bigint} value
     * @param {bigint} asset_type
     * @returns {any}
     */
    function create_note(handle, agent_index, value, asset_type) {
        const ret = wasm.create_note(handle, agent_index, value, asset_type);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_note = create_note;

    /**
     * Sign a state-transition for the named agent's exchange session and
     * return the postcard-encoded `PeerStateTransition` bytes. Bytes — not
     * JSON — because the whole point is a compact signed blob that can be
     * base64-encoded for paste UX.
     * @param {number} handle
     * @param {number} agent_idx
     * @param {string} old_commit_hex
     * @param {string} new_commit_hex
     * @param {string} effects_hash_hex
     * @returns {Uint8Array}
     */
    function create_peer_transition(handle, agent_idx, old_commit_hex, new_commit_hex, effects_hash_hex) {
        const ptr0 = passStringToWasm0(old_commit_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(new_commit_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(effects_hash_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ret = wasm.create_peer_transition(handle, agent_idx, ptr0, len0, ptr1, len1, ptr2, len2);
        if (ret[3]) {
            throw takeFromExternrefTable0(ret[2]);
        }
        var v4 = getArrayU8FromWasm0(ret[0], ret[1]).slice();
        wasm.__wbindgen_free(ret[0], ret[1] * 1, 1);
        return v4;
    }
    exports.create_peer_transition = create_peer_transition;

    /**
     * Create a revocation channel for an agent.
     * @param {number} handle
     * @param {number} revoker_agent
     * @returns {any}
     */
    function create_revocation_channel(handle, revoker_agent) {
        const ret = wasm.create_revocation_channel(handle, revoker_agent);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_revocation_channel = create_revocation_channel;

    /**
     * Create a new DreggRuntime and return its handle.
     * @returns {number}
     */
    function create_runtime() {
        const ret = wasm.create_runtime();
        return ret >>> 0;
    }
    exports.create_runtime = create_runtime;

    /**
     * Create a one-time stealth address for a recipient.
     *
     * Implements the stealth address protocol using X25519 DH:
     * 1. Generate ephemeral X25519 keypair
     * 2. Compute shared_secret = X25519(ephemeral_priv, recipient_view_pubkey)
     * 3. Derive scalar = BLAKE3(shared_secret, "dregg-stealth-derive")
     * 4. one_time_pubkey = H(scalar || spend_pubkey) (simplified for WASM)
     *
     * Returns JSON: { one_time_pubkey, ephemeral_pubkey }
     * @param {Uint8Array} recipient_spend_pubkey
     * @param {Uint8Array} recipient_view_pubkey
     * @returns {any}
     */
    function create_stealth_address(recipient_spend_pubkey, recipient_view_pubkey) {
        const ptr0 = passArray8ToWasm0(recipient_spend_pubkey, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(recipient_view_pubkey, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.create_stealth_address(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_stealth_address = create_stealth_address;

    /**
     * Create a **real** Pedersen value commitment over the Ristretto group.
     *
     * `commitment = amount * V + scalar(blinding) * R`, where `V`/`R` are the
     * canonical `dregg_cell` value/randomness generators and the 32 blinding bytes
     * are reduced mod the group order into a `Scalar`. The returned `commitment`
     * is the 32-byte compressed Ristretto encoding — the exact bytes that
     * `verify_conservation_proof` / `prove_conservation` consume and that
     * `ValueCommitment::to_bytes` produces. This replaces the previous BLAKE3
     * hash placeholder, which was NOT a real curve point and was incompatible with
     * the homomorphic conservation verifier.
     *
     * Returns JSON: { commitment: Vec<u8> (32-byte compressed Ristretto), blinding: Vec<u8> }
     * @param {bigint} amount
     * @param {Uint8Array} blinding
     * @returns {any}
     */
    function create_value_commitment(amount, blinding) {
        const ptr0 = passArray8ToWasm0(blinding, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.create_value_commitment(amount, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.create_value_commitment = create_value_commitment;

    /**
     * Compute the canonical custom signing message a `commit_table_update` action
     * (with the given effects) binds to. Returns lowercase hex. Committee members
     * sign these exact bytes via `sign_custom_commit`.
     * @param {number} handle
     * @param {number} agent_index
     * @param {string} target_cell_id_hex
     * @param {string} method
     * @param {string} actions_json
     * @param {string} vk_hash_hex
     * @param {string} committee_commitment_hex
     * @returns {string}
     */
    function custom_commit_signing_message(handle, agent_index, target_cell_id_hex, method, actions_json, vk_hash_hex, committee_commitment_hex) {
        let deferred7_0;
        let deferred7_1;
        try {
            const ptr0 = passStringToWasm0(target_cell_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len0 = WASM_VECTOR_LEN;
            const ptr1 = passStringToWasm0(method, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len1 = WASM_VECTOR_LEN;
            const ptr2 = passStringToWasm0(actions_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len2 = WASM_VECTOR_LEN;
            const ptr3 = passStringToWasm0(vk_hash_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len3 = WASM_VECTOR_LEN;
            const ptr4 = passStringToWasm0(committee_commitment_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len4 = WASM_VECTOR_LEN;
            const ret = wasm.custom_commit_signing_message(handle, agent_index, ptr0, len0, ptr1, len1, ptr2, len2, ptr3, len3, ptr4, len4);
            var ptr6 = ret[0];
            var len6 = ret[1];
            if (ret[3]) {
                ptr6 = 0; len6 = 0;
                throw takeFromExternrefTable0(ret[2]);
            }
            deferred7_0 = ptr6;
            deferred7_1 = len6;
            return getStringFromWasm0(ptr6, len6);
        } finally {
            wasm.__wbindgen_free(deferred7_0, deferred7_1, 1);
        }
    }
    exports.custom_commit_signing_message = custom_commit_signing_message;

    /**
     * Postcard-decode a `PeerStateTransition` and return its fields as a
     * structured JS object. The transition_bytes are the raw postcard bytes
     * returned by `create_peer_transition`.
     *
     * Returns `{ cell_id, old_commitment, new_commitment, effects_hash,
     *   timestamp, sequence, signature, has_transition_proof }`.
     * Full proof bytes are NOT included by default (too large for render);
     * `has_transition_proof: bool` tells the inspector whether one is
     * attached.
     * @param {Uint8Array} bytes
     * @returns {any}
     */
    function decode_peer_transition(bytes) {
        const ptr0 = passArray8ToWasm0(bytes, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.decode_peer_transition(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.decode_peer_transition = decode_peer_transition;

    /**
     * Return the VK of the runtime's default test-cipherclerk factory — the
     * factory used by `create_agent` / `create_cell` when no explicit
     * factory is named.
     *
     * Exposed so the JS layer can pre-register the wasm-runtime factory
     * set with `verifyProvenance` (or display the wasm-runtime's
     * constructor-transparency anchor in the inspector UI).
     * @param {number} handle
     * @returns {any}
     */
    function default_factory_vk(handle) {
        const ret = wasm.default_factory_vk(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.default_factory_vk = default_factory_vk;

    /**
     * Create a token state, attenuate it, and return the fold chain info.
     *
     * `facts_json`: array of strings like "predicate:term1:term2"
     * `remove_json`: array of strings (facts to remove in attenuation)
     *
     * Returns JSON with old_root, new_root, verification status.
     * @param {string} facts_json
     * @param {string} remove_json
     * @returns {any}
     */
    function demonstrate_fold(facts_json, remove_json) {
        const ptr0 = passStringToWasm0(facts_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(remove_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.demonstrate_fold(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.demonstrate_fold = demonstrate_fold;

    /**
     * **`deploy_check(text, ring)`** — parse DreggDL → lower to the real
     * `CallForest` → run `dregg_userspace_verify::analyze` over the whole declared
     * authority layout → return the `DeployVerdict` as a JSON string
     * (`{pass, assurance, factories, cells, turn_count}`).
     *
     * This is exactly `dregg-deploy check`. On a parse / lowering error returns a
     * `JsError` naming the offending row.
     * @param {string} text
     * @param {boolean} ring
     * @returns {string}
     */
    function deploy_check(text, ring) {
        let deferred3_0;
        let deferred3_1;
        try {
            const ptr0 = passStringToWasm0(text, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.deploy_check(ptr0, len0, ring);
            var ptr2 = ret[0];
            var len2 = ret[1];
            if (ret[3]) {
                ptr2 = 0; len2 = 0;
                throw takeFromExternrefTable0(ret[2]);
            }
            deferred3_0 = ptr2;
            deferred3_1 = len2;
            return getStringFromWasm0(ptr2, len2);
        } finally {
            wasm.__wbindgen_free(deferred3_0, deferred3_1, 1);
        }
    }
    exports.deploy_check = deploy_check;

    /**
     * Deploy a factory descriptor into the runtime, returning the
     * `factory_vk` that addresses it. The factory_vk can then be passed to
     * [`create_agent_with_factory`] (or to JS-side `createFromFactory`)
     * to mint cells from this factory.
     *
     * `descriptor_json` is a serde-serialized `FactoryDescriptor`. Apps
     * that ship their own factories can call this at boot to register them
     * alongside the runtime's default test-cipherclerk factory.
     * @param {number} handle
     * @param {string} descriptor_json
     * @returns {any}
     */
    function deploy_factory_descriptor(handle, descriptor_json) {
        const ptr0 = passStringToWasm0(descriptor_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.deploy_factory_descriptor(handle, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.deploy_factory_descriptor = deploy_factory_descriptor;

    /**
     * **`deploy_lower(text)`** — run only the real `Lowered::from_deployment`
     * lowering (no check) and return `{forest, federation_id, factories, cells}`
     * as a JSON string, where `forest` is the ordered births → funds → grants
     * `CallForest` the checker consumes. This is `dregg-deploy lower`.
     * @param {string} text
     * @returns {string}
     */
    function deploy_lower(text) {
        let deferred3_0;
        let deferred3_1;
        try {
            const ptr0 = passStringToWasm0(text, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.deploy_lower(ptr0, len0);
            var ptr2 = ret[0];
            var len2 = ret[1];
            if (ret[3]) {
                ptr2 = 0; len2 = 0;
                throw takeFromExternrefTable0(ret[2]);
            }
            deferred3_0 = ptr2;
            deferred3_1 = len2;
            return getStringFromWasm0(ptr2, len2);
        } finally {
            wasm.__wbindgen_free(deferred3_0, deferred3_1, 1);
        }
    }
    exports.deploy_lower = deploy_lower;

    /**
     * Derive an Ed25519 keypair from a BIP39 mnemonic using the dregg BLAKE3 derivation path.
     *
     * This uses the same BLAKE3-based derivation as `dregg-sdk`'s `mnemonic_to_seed` +
     * `derive_keypair`. The Ed25519 public key is computed in-WASM via ed25519-dalek.
     *
     * Returns an object `{ public_key: Vec<u8>(32), secret_key: Vec<u8>(32) }`.
     *
     * # Arguments
     * * `mnemonic` - A 24-word BIP39 mnemonic string.
     * * `passphrase` - Optional passphrase (use empty string for none).
     *
     * # Errors
     * Returns an error if the mnemonic is invalid.
     *
     * # Security
     * Intermediate seed material is wrapped in `Zeroizing` to scrub linear-memory
     * residues on drop. The returned secret/public key bytes are necessarily
     * copied into a JS object by `serde_wasm_bindgen`; callers in background
     * workers should overwrite or drop those buffers when done.
     * @param {string} mnemonic
     * @param {string} passphrase
     * @returns {any}
     */
    function derive_keypair_from_mnemonic(mnemonic, passphrase) {
        const ptr0 = passStringToWasm0(mnemonic, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(passphrase, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.derive_keypair_from_mnemonic(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.derive_keypair_from_mnemonic = derive_keypair_from_mnemonic;

    /**
     * Derive stealth keys from a mnemonic + passphrase.
     *
     * Returns JSON: { spend_pubkey, spend_privkey, view_pubkey, view_privkey }
     * All keys are 32-byte arrays. The public keys are BLAKE3 derivations of the
     * private keys (matching the SDK's deterministic derivation). The extension uses
     * these with its own Ed25519/X25519 library for the full DH protocol.
     * @param {string} mnemonic
     * @param {string} passphrase
     * @returns {any}
     */
    function derive_stealth_keys(mnemonic, passphrase) {
        const ptr0 = passStringToWasm0(mnemonic, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(passphrase, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.derive_stealth_keys(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.derive_stealth_keys = derive_stealth_keys;

    /**
     * Alias matching the extension's expected export name.
     * @param {Uint8Array} recipient_spend_pubkey
     * @param {Uint8Array} recipient_view_pubkey
     * @returns {any}
     */
    function derive_stealth_one_time_address(recipient_spend_pubkey, recipient_view_pubkey) {
        const ptr0 = passArray8ToWasm0(recipient_spend_pubkey, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(recipient_view_pubkey, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.derive_stealth_one_time_address(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.derive_stealth_one_time_address = derive_stealth_one_time_address;

    /**
     * Destroy a runtime, freeing its resources. Returns true if the handle was valid.
     * @param {number} handle
     * @returns {boolean}
     */
    function destroy_runtime(handle) {
        const ret = wasm.destroy_runtime(handle);
        return ret !== 0;
    }
    exports.destroy_runtime = destroy_runtime;

    /**
     * Evaluate a Datalog authorization request against facts and rules.
     *
     * `facts_json`: array of { "predicate": "name", "terms": ["const1", "const2"] }
     * `request_json`: { "app_id": "...", "action": "...", "service": "..." }
     *
     * Returns the full derivation trace as JSON.
     * @param {string} facts_json
     * @param {string} request_json
     * @returns {any}
     */
    function evaluate_datalog(facts_json, request_json) {
        const ptr0 = passStringToWasm0(facts_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(request_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.evaluate_datalog(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.evaluate_datalog = evaluate_datalog;

    /**
     * Execute a real signed multi-agent app turn: `agent_index` signs, the action
     * targets `target_cell_id_hex` with method `method`, carrying the effects in
     * `actions_json` (same shape as `execute_turn`, now including `emit_event`).
     * @param {number} handle
     * @param {number} agent_index
     * @param {string} target_cell_id_hex
     * @param {string} method
     * @param {string} actions_json
     * @param {bigint} fee
     * @returns {any}
     */
    function execute_app_turn(handle, agent_index, target_cell_id_hex, method, actions_json, fee) {
        const ptr0 = passStringToWasm0(target_cell_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(method, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(actions_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ret = wasm.execute_app_turn(handle, agent_index, ptr0, len0, ptr1, len1, ptr2, len2, fee);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.execute_app_turn = execute_app_turn;

    /**
     * Execute a real `Authorization::Custom` commit turn. `proof_hex` is the
     * concatenation of `threshold` 96-byte `(pubkey ‖ sig)` records (hex) produced
     * by `sign_custom_commit`. The turn is accepted only if the registered
     * threshold verifier validates the signatures over the canonical message and
     * the cell-program's `MonotonicSequence(version)` caveat accepts the +1 bump.
     * @param {number} handle
     * @param {number} agent_index
     * @param {string} target_cell_id_hex
     * @param {string} method
     * @param {string} actions_json
     * @param {string} vk_hash_hex
     * @param {string} committee_commitment_hex
     * @param {string} proof_hex
     * @param {bigint} fee
     * @returns {any}
     */
    function execute_custom_auth_turn(handle, agent_index, target_cell_id_hex, method, actions_json, vk_hash_hex, committee_commitment_hex, proof_hex, fee) {
        const ptr0 = passStringToWasm0(target_cell_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(method, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(actions_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ptr3 = passStringToWasm0(vk_hash_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len3 = WASM_VECTOR_LEN;
        const ptr4 = passStringToWasm0(committee_commitment_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len4 = WASM_VECTOR_LEN;
        const ptr5 = passStringToWasm0(proof_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len5 = WASM_VECTOR_LEN;
        const ret = wasm.execute_custom_auth_turn(handle, agent_index, ptr0, len0, ptr1, len1, ptr2, len2, ptr3, len3, ptr4, len4, ptr5, len5, fee);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.execute_custom_auth_turn = execute_custom_auth_turn;

    /**
     * Build and execute a turn for an agent.
     *
     * `actions_json` is a JSON array of action descriptors:
     * ```json
     * [
     *   { "type": "transfer", "to": "<cell_id_hex>", "amount": 100 },
     *   { "type": "set_field", "cell": "<cell_id_hex>", "index": 0, "value_hex": "..." },
     *   { "type": "increment_nonce", "cell": "<cell_id_hex>" }
     * ]
     * ```
     * @param {number} handle
     * @param {number} agent_index
     * @param {string} actions_json
     * @param {bigint} fee
     * @returns {any}
     */
    function execute_turn(handle, agent_index, actions_json, fee) {
        const ptr0 = passStringToWasm0(actions_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.execute_turn(handle, agent_index, ptr0, len0, fee);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.execute_turn = execute_turn;

    /**
     * Execute a turn step-by-step and return the execution trace.
     * Same input format as `execute_turn` but returns detailed trace info.
     * @param {number} handle
     * @param {number} agent_index
     * @param {string} actions_json
     * @param {bigint} fee
     * @returns {any}
     */
    function execute_turn_step_by_step(handle, agent_index, actions_json, fee) {
        const ptr0 = passStringToWasm0(actions_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.execute_turn_step_by_step(handle, agent_index, ptr0, len0, fee);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.execute_turn_step_by_step = execute_turn_step_by_step;

    /**
     * Export runtime snapshot stub (STARBRIDGE-FOLLOWUP-03 on blocked §5.9).
     *
     * Returns pretty JSON with current state summary + explicit note that
     * this is a v0 placeholder pending the canonical WitnessedReceipt stream
     * format (Houyhnhnm + plan §8 Q4). Unblocks JS/inspector prep for
     * snapshot-and-replay / time-travel without requiring the human cargo
     * session for proving changes. Matches the Rust surface added to
     * DreggRuntime::export_runtime_snapshot_stub.
     *
     * Safe thin binding (delegates only; no new crypto, no circuit).
     * @param {number} handle
     * @returns {string}
     */
    function export_runtime_snapshot_stub(handle) {
        let deferred2_0;
        let deferred2_1;
        try {
            const ret = wasm.export_runtime_snapshot_stub(handle);
            var ptr1 = ret[0];
            var len1 = ret[1];
            if (ret[3]) {
                ptr1 = 0; len1 = 0;
                throw takeFromExternrefTable0(ret[2]);
            }
            deferred2_0 = ptr1;
            deferred2_1 = len1;
            return getStringFromWasm0(ptr1, len1);
        } finally {
            wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
        }
    }
    exports.export_runtime_snapshot_stub = export_runtime_snapshot_stub;

    /**
     * Run the full garbled circuit comparison protocol (both parties in-process for demo).
     *
     * Proves `prover_value >= verifier_threshold` without the prover learning the threshold
     * (garbled circuit approach). Both parties are simulated in-process for the playground.
     *
     * Returns JSON with: result (pass/fail), proof_size, garbling_time_ms
     * @param {number} prover_value
     * @param {number} verifier_threshold
     * @returns {any}
     */
    function garbled_compare(prover_value, verifier_threshold) {
        const ret = wasm.garbled_compare(prover_value, verifier_threshold);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.garbled_compare = garbled_compare;

    /**
     * Generates a REAL arity-4 Poseidon2 Merkle-membership proof as an
     * `Ir2BatchProof`, wrapped in the serde_json `Ir2ProofEnvelope` wire (the
     * StarkProof->Ir2BatchProof migration). `leaf_value` is a u32 field element;
     * `depth` is snapped to a power of two in `{2, 4, 8}`. The returned
     * `proof_json` feeds straight into `verify_demo_stark_proof`.
     *
     * Returns JSON with the envelope, generation time, proof size, and the
     * descriptor dispatch name.
     * @param {number} leaf_value
     * @param {number} depth
     * @returns {any}
     */
    function generate_demo_stark_proof(leaf_value, depth) {
        const ret = wasm.generate_demo_stark_proof(leaf_value, depth);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.generate_demo_stark_proof = generate_demo_stark_proof;

    /**
     * Generate a predicate proof for a private attribute.
     *
     * Proves a comparison statement about `private_value` vs `threshold` without
     * revealing the private value. The proof is bound to a fact commitment derived
     * from the attribute key and a state root.
     *
     * `predicate_type`: "gte", "lte", "gt", "lt", "neq"
     * `private_value`: The secret value (u32 field element)
     * `threshold`: The public comparison target (u32 field element)
     * `attribute_key`: String key used to derive the fact hash
     * `state_root`: A u32 field element representing the token state root
     *
     * Returns JSON with proof data, or an error if the predicate is not satisfiable.
     * @param {string} predicate_type
     * @param {number} private_value
     * @param {number} threshold
     * @param {string} attribute_key
     * @param {number} state_root
     * @returns {any}
     */
    function generate_predicate_proof(predicate_type, private_value, threshold, attribute_key, state_root) {
        const ptr0 = passStringToWasm0(predicate_type, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(attribute_key, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.generate_predicate_proof(ptr0, len0, private_value, threshold, ptr1, len1, state_root);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.generate_predicate_proof = generate_predicate_proof;

    /**
     * Generate a **real** Bulletproof range proof that a committed value is in
     * `[0, 2^64)`.
     *
     * This builds the canonical Pedersen commitment `value*V + scalar(blinding)*R`
     * over Ristretto and a real `bulletproofs::RangeProof` (curve25519-dalek,
     * runs natively on wasm32). The `_commitment` argument is ignored — the
     * commitment is recomputed from `(amount, blinding)` so the returned
     * `commitment` is guaranteed to match the proof. Feed `commitment` +
     * `range_proof` straight to [`verify_range_proof`].
     *
     * Returns JSON: `{ commitment: Vec<u8> (32B), range_proof: Vec<u8> (~672B),
     * proof_size_bytes: usize }`. (`proof` is kept as an alias of `range_proof`
     * for callers that read the old field name.)
     * @param {bigint} amount
     * @param {Uint8Array} blinding
     * @param {Uint8Array} _commitment
     * @returns {any}
     */
    function generate_range_proof(amount, blinding, _commitment) {
        const ptr0 = passArray8ToWasm0(blinding, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(_commitment, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.generate_range_proof(amount, ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.generate_range_proof = generate_range_proof;

    /**
     * Generate a random 32-byte root key and return it as hex.
     * @returns {any}
     */
    function generate_root_key() {
        const ret = wasm.generate_root_key();
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.generate_root_key = generate_root_key;

    /**
     * Generate searchable symmetric encryption (SSE) tokens from keywords.
     *
     * Returns a flat byte array: N tokens of 32 bytes each.
     * @param {string} keywords_json
     * @returns {Uint8Array}
     */
    function generate_sse_tokens(keywords_json) {
        const ptr0 = passStringToWasm0(keywords_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.generate_sse_tokens(ptr0, len0);
        if (ret[3]) {
            throw takeFromExternrefTable0(ret[2]);
        }
        var v2 = getArrayU8FromWasm0(ret[0], ret[1]).slice();
        wasm.__wbindgen_free(ret[0], ret[1] * 1, 1);
        return v2;
    }
    exports.generate_sse_tokens = generate_sse_tokens;

    /**
     * Fold a real `k`-turn chain (the same shape [`light_client_demo`] folds) and
     * return its root-circuit **VK fingerprint** as hex — the CONFIG TRUST ANCHOR a
     * genesis/checkpoint configuration distributes.
     *
     * The fingerprint is a function of the root circuit SHAPE (window size + leaf
     * trace heights), NOT of the folded history's content — two different `k`-turn
     * histories of the same shape fingerprint identically (the load-bearing anchor
     * property, proven in `dregg-lightclient`'s `vk_anchor_is_circuit_shape_not_
     * history_content`). So this is exactly the value an honest setup mints ONCE and
     * ships in config; a verifier then holds it SEPARATELY from any artifact and
     * checks every aggregate of that shape against it.
     *
     * `k` is clamped to `[2, 4]` (same as the demo). Returns the 64-char hex anchor.
     * @param {number} k
     * @param {bigint} step
     * @returns {string}
     */
    function genesis_vk_anchor(k, step) {
        let deferred2_0;
        let deferred2_1;
        try {
            const ret = wasm.genesis_vk_anchor(k, step);
            var ptr1 = ret[0];
            var len1 = ret[1];
            if (ret[3]) {
                ptr1 = 0; len1 = 0;
                throw takeFromExternrefTable0(ret[2]);
            }
            deferred2_0 = ptr1;
            deferred2_1 = len1;
            return getStringFromWasm0(ptr1, len1);
        } finally {
            wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
        }
    }
    exports.genesis_vk_anchor = genesis_vk_anchor;

    /**
     * Get the receipt chain filtered to a single agent.
     *
     * The wasm sim runtime applies turns through one shared `TurnExecutor` and
     * records receipts in `DreggRuntime::receipts` (the cipherclerk's own
     * `receipt_chain()` is not threaded in the sim path). Each `TurnReceipt`
     * carries its `agent: CellId`, so we filter the global chain by the agent's
     * cell id — the honest per-agent view. Same `ReceiptView` shape as
     * `get_receipt_chain`, minus the per-action/proof expansion (the inspector
     * drills into individual receipts via `<dregg-receipt uri="...">`).
     * @param {number} handle
     * @param {number} agent_index
     * @returns {any}
     */
    function get_agent_receipts(handle, agent_index) {
        const ret = wasm.get_agent_receipts(handle, agent_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_agent_receipts = get_agent_receipts;

    /**
     * Get an agent's stealth meta-address — the view and spend PUBLIC keys only.
     *
     * Sourced from `AgentCipherclerk::stealth_meta_address()`
     * (`StealthMetaAddress { spend_pubkey, view_pubkey }`). The corresponding
     * PRIVATE keys (`view_private_key` / `spend_private_key`) are NEVER surfaced —
     * they stay inside the cipherclerk's `StealthKeys`. Publishing the meta-address
     * is the intended use: senders derive unlinkable one-time addresses from it.
     * @param {number} handle
     * @param {number} agent_index
     * @returns {any}
     */
    function get_agent_stealth_keys(handle, agent_index) {
        const ret = wasm.get_agent_stealth_keys(handle, agent_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_agent_stealth_keys = get_agent_stealth_keys;

    /**
     * List the macaroon-backed `HeldToken`s held by an agent's cipherclerk
     * (`AgentCipherclerk::tokens()`). Distinct from the intent-matcher
     * `HeldCapability` list surfaced by `get_capability_tree`.
     *
     * Returns a JSON array of token summaries. No `root_key` / `issuer_key` is
     * surfaced (those are `#[serde(skip)]` and zeroed on drop in the SDK); only the
     * public-facing macaroon fields plus the capability flags (`can_mint`,
     * `can_prove`, `verified`) are exposed.
     * @param {number} handle
     * @param {number} agent_index
     * @returns {any}
     */
    function get_agent_tokens(handle, agent_index) {
        const ret = wasm.get_agent_tokens(handle, agent_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_agent_tokens = get_agent_tokens;

    /**
     * Get all cells in the ledger.
     * @param {number} handle
     * @returns {any}
     */
    function get_all_cells(handle) {
        const ret = wasm.get_all_cells(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_all_cells = get_all_cells;

    /**
     * Get the capability tree (CDT) for an agent's cell.
     * @param {number} handle
     * @param {number} agent_index
     * @returns {any}
     */
    function get_capability_tree(handle, agent_index) {
        const ret = wasm.get_capability_tree(handle, agent_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_capability_tree = get_capability_tree;

    /**
     * Get the state of a cell.
     *
     * Refactor 6: adds `program: CellProgramView` surfacing the full slot-caveat
     * tree so JS inspectors can render a complete picture of the cell's program
     * semantics. Existing fields are byte-equivalent to the prior shape.
     * @param {number} handle
     * @param {string} cell_id_hex
     * @returns {any}
     */
    function get_cell_state(handle, cell_id_hex) {
        const ptr0 = passStringToWasm0(cell_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.get_cell_state(handle, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_cell_state = get_cell_state;

    /**
     * Read the current canonical state-commitment of a cell — what the agent
     * signs over when emitting a `PeerStateTransition`. Returns `null` if the
     * cell isn't in the ledger.
     * @param {number} handle
     * @param {string} cell_id_hex
     * @returns {any}
     */
    function get_cell_state_commitment(handle, cell_id_hex) {
        const ptr0 = passStringToWasm0(cell_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.get_cell_state_commitment(handle, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_cell_state_commitment = get_cell_state_commitment;

    /**
     * Get the delegation graph (all capabilities across all cells).
     * @param {number} handle
     * @returns {any}
     */
    function get_delegation_graph(handle) {
        const ret = wasm.get_delegation_graph(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_delegation_graph = get_delegation_graph;

    /**
     * Get a finalized block by height (1-indexed; height 1 = first finalized
     * block). Returns `null` if the height has not been finalized.
     * @param {number} handle
     * @param {number} fed_index
     * @param {bigint} height
     * @returns {any}
     */
    function get_federation_block(handle, fed_index, height) {
        const ret = wasm.get_federation_block(handle, fed_index, height);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_federation_block = get_federation_block;

    /**
     * Get a snapshot of federation state — node count, finalized history depth,
     * latest attested root, etc. All values derived from the canonical
     * `Federation` committee + local consensus state.
     * @param {number} handle
     * @param {number} fed_index
     * @returns {any}
     */
    function get_federation_state(handle, fed_index) {
        const ret = wasm.get_federation_state(handle, fed_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_federation_state = get_federation_state;

    /**
     * Get the Merkle tree visualization data (for SVG rendering).
     * @param {number} handle
     * @returns {any}
     */
    function get_merkle_tree_viz(handle) {
        const ret = wasm.get_merkle_tree_viz(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_merkle_tree_viz = get_merkle_tree_viz;

    /**
     * List notes for an agent. Returns array of
     * `{commitment, value, asset_type, spent, nullifier}`.
     *
     * Reads the agent's real `held_notes` index (#45): every note minted via
     * `create_note` is recorded there (and marked spent — with its revealed
     * nullifier — once `spend_note` runs). `commitment` / `value` / `asset_type`
     * are derived from the canonical `dregg_cell::Note`, so the `<dregg-note>`
     * inspector and `dregg://note/<commitment>` URI lookups resolve real data
     * rather than the prior always-empty stub. `nullifier` is `null` until spent.
     * @param {number} handle
     * @param {number} agent_index
     * @returns {any}
     */
    function get_notes(handle, agent_index) {
        const ret = wasm.get_notes(handle, agent_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_notes = get_notes;

    /**
     * Convenience: get the agent's PeerExchange public key. Useful for the
     * paste-UX where one side needs to share the verifying key with the
     * other up-front.
     * @param {number} handle
     * @param {number} agent_idx
     * @returns {any}
     */
    function get_peer_pubkey(handle, agent_idx) {
        const ret = wasm.get_peer_pubkey(handle, agent_idx);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_peer_pubkey = get_peer_pubkey;

    /**
     * Read the agent's current view of a peer cell — commitment, sequence,
     * timestamp. Returns `null` if the peer has not been registered.
     * @param {number} handle
     * @param {number} agent_idx
     * @param {string} peer_cell_id_hex
     * @returns {any}
     */
    function get_peer_view(handle, agent_idx, peer_cell_id_hex) {
        const ptr0 = passStringToWasm0(peer_cell_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.get_peer_view(handle, agent_idx, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_peer_view = get_peer_view;

    /**
     * List pending conditional turns in the runtime (for <dregg-conditional-turn>).
     * Uses the real PendingConditional vec from runtime; condition simplified to string tag.
     * @param {number} handle
     * @returns {any}
     */
    function get_pending_conditionals(handle) {
        const ret = wasm.get_pending_conditionals(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_pending_conditionals = get_pending_conditionals;

    /**
     * Get the receipt chain for the runtime.
     *
     * Refactor 3: adds `actions: Vec<ActionView>` per receipt, each with
     * `target_cell`, `method`, `effects`, and `authorization` (6-variant tagged union).
     * Refactor 7: adds `proof_view: Option<ProofView>` per receipt for γ.2 bilateral
     * PI rendering by `<dregg-proof>`.
     * Existing fields are byte-equivalent to the prior shape.
     * @param {number} handle
     * @returns {any}
     */
    function get_receipt_chain(handle) {
        const ret = wasm.get_receipt_chain(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_receipt_chain = get_receipt_chain;

    /**
     * Return the current dregg-observability event log as the Studio wire JSON
     * (schema with "schema_version", "events": [{kind, envelope, payload}, ...]).
     * This is the source for the signal-cached getter in runtime-in-memory.js
     * and the <dregg-activity> live feed inspector (Task #30).
     *
     * The log contains TurnLifecycle (at minimum; full 7 variants when deeper
     * executor hooks land) plus any future Authorization etc. events.
     * @param {number} handle
     * @returns {any}
     */
    function get_trace_events_json(handle) {
        const ret = wasm.get_trace_events_json(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_trace_events_json = get_trace_events_json;

    /**
     * Return trace steps for the committed turn identified by `turn_hash_hex`.
     * If the turn is not found in the receipt chain, returns `null`.
     *
     * Each step: `{ action_path: number[], target_cell: string, method: string,
     *   effects: string[], computrons_used: number, result: string }`.
     * @param {number} handle
     * @param {string} turn_hash_hex
     * @returns {any}
     */
    function get_turn_trace(handle, turn_hash_hex) {
        const ptr0 = passStringToWasm0(turn_hash_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.get_turn_trace(handle, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.get_turn_trace = get_turn_trace;

    /**
     * Grant a capability from one agent to another.
     * @param {number} handle
     * @param {number} from_agent
     * @param {number} to_agent
     * @param {string} target_cell_hex
     * @param {string} permission
     * @returns {any}
     */
    function grant_capability(handle, from_agent, to_agent, target_cell_hex, permission) {
        const ptr0 = passStringToWasm0(target_cell_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(permission, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.grant_capability(handle, from_agent, to_agent, ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.grant_capability = grant_capability;

    /**
     * Grant the acting agent's cell a capability to reach `target_cell_id_hex`.
     * Required before a non-owner agent can drive a turn against an app cell.
     * @param {number} handle
     * @param {number} agent_index
     * @param {string} target_cell_id_hex
     * @returns {any}
     */
    function grant_reach_capability(handle, agent_index, target_cell_id_hex) {
        const ptr0 = passStringToWasm0(target_cell_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.grant_reach_capability(handle, agent_index, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.grant_reach_capability = grant_reach_capability;

    /**
     * Install a canonical starbridge-app cell-program + initial state on a cell.
     *
     * `program_kind`:
     *   - `"subscription"` — installs `subscription_program` (CapInbox shape).
     *     `owner_pk_hash_hex` seeds slot 5; `capacity` seeds slot 2.
     *   - `"governed-namespace"` — installs `governance_program`.
     *     `committee_root_hex` seeds slot 2; `threshold` seeds slot 3;
     *     `initial_route_table_root_hex` seeds slot 0.
     *   - `"escrow"` — installs `escrow_program` (compute-marketplace shape).
     *     `budget` seeds slot 1 (frozen); `job_hash_hex` seeds slot 3 (frozen);
     *     phase slot 0 is one-way (settle/dispute drain the real balance once).
     *
     * Permissions are opened so multi-agent turns apply; the slot-caveat
     * cell-program is the load-bearing enforcement (mirrors the apps' executor
     * integration-test harness exactly).
     * @param {number} handle
     * @param {string} cell_id_hex
     * @param {string} program_kind
     * @param {string} config_json
     * @returns {any}
     */
    function install_app_program(handle, cell_id_hex, program_kind, config_json) {
        const ptr0 = passStringToWasm0(cell_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(program_kind, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(config_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ret = wasm.install_app_program(handle, ptr0, len0, ptr1, len1, ptr2, len2);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.install_app_program = install_app_program;

    /**
     * Check if a revocation channel is active.
     * @param {number} handle
     * @param {string} channel_id_hex
     * @returns {any}
     */
    function is_channel_active(handle, channel_id_hex) {
        const ptr0 = passStringToWasm0(channel_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.is_channel_active(handle, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.is_channel_active = is_channel_active;

    /**
     * **THE IN-TAB LIGHT CLIENT** — fold a real `k`-turn chain in wasm32 and
     * light-verify it, re-witnessing nothing.
     *
     * Each turn debits `step` from a running balance; each leaf is a REAL
     * Lean-descriptor EffectVM proof (`prove_vm_descriptor`, the audited p3 batch
     * prover — the same wire artifact the SDK cutover emits) verified in-circuit by
     * the recursion wrap. The fold is the expensive step (done once); the
     * light-client verify is the cheap step. SELF-ANCHORS: the VK fingerprint is
     * minted from the locally produced fold (the honest setup mint).
     *
     * `k` is clamped to `[2, 4]` — the recursive chain-binding folds the temporal
     * `new_root[i] == old_root[i+1]` tooth, so it needs AT LEAST 2 turns; and
     * recursive proving in a browser is heavy, so a small chain keeps the demo
     * responsive while exercising the REAL pipeline end-to-end.
     *
     * Returns an [`AttestedHistoryView`]. Errors only on an internal substrate bug
     * (a chain that should fold but doesn't), which the caller surfaces honestly.
     * @param {number} k
     * @param {bigint} step
     * @returns {any}
     */
    function light_client_demo(k, step) {
        const ret = wasm.light_client_demo(k, step);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.light_client_demo = light_client_demo;

    /**
     * List every factory deployed in the runtime's executor (read path for
     * `<dregg-factory-descriptor>`).
     *
     * Walks the canonical `executor.factory_registry` (`FactoryRegistry::descriptors`)
     * and surfaces each deployed `FactoryDescriptor`'s real metadata: its VK, the
     * counts of state/field constraints and allowed capability templates, default
     * cell mode, optional child program VK, and creation budget. The runtime's
     * default test-cipherclerk factory is flagged so the inspector can distinguish
     * it. This replaces the prior coarse stub that hardcoded `has_state_constraints:
     * false` and only ever returned the default VK.
     * @param {number} handle
     * @returns {any}
     */
    function list_deployed_factories(handle) {
        const ret = wasm.list_deployed_factories(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.list_deployed_factories = list_deployed_factories;

    /**
     * List all finalized block headers for a federation. Each entry is a
     * compact summary; call `get_federation_block(fed_idx, height)` for the
     * full view. Returns an empty list if nothing has been finalized.
     * @param {number} handle
     * @param {number} fed_index
     * @returns {any}
     */
    function list_federation_blocks(handle, fed_index) {
        const ret = wasm.list_federation_blocks(handle, fed_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.list_federation_blocks = list_federation_blocks;

    /**
     * List the KnownFederations registry (wasm/sim surface for §5.7).
     * Returns the SimFederations the runtime knows (analog to node
     * KnownFederations for the federation-list inspector).
     * @param {number} handle
     * @returns {any}
     */
    function list_known_federations(handle) {
        const ret = wasm.list_known_federations(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.list_known_federations = list_known_federations;

    /**
     * List all peer cell ids the agent has registered (hex strings).
     * @param {number} handle
     * @param {number} agent_idx
     * @returns {any}
     */
    function list_peers(handle, agent_idx) {
        const ret = wasm.list_peers(handle, agent_idx);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.list_peers = list_peers;

    /**
     * List all known revocation channels (ids + active state). Now uses real
     * RevocationChannelSet::iter() (the TODO is resolved; inspector cluster A).
     * Enables <dregg-revocation-channel> list + URI views with live state.
     * @param {number} handle
     * @returns {any}
     */
    function list_revocation_channels(handle) {
        const ret = wasm.list_revocation_channels(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.list_revocation_channels = list_revocation_channels;

    /**
     * Create the make_sovereign effect payload.
     *
     * Returns the BLAKE3 commitment of the cell state that the federation will store.
     * @param {string} cell_id_hex
     * @param {bigint} current_balance
     * @returns {any}
     */
    function make_cell_sovereign(cell_id_hex, current_balance) {
        const ptr0 = passStringToWasm0(cell_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.make_cell_sovereign(ptr0, len0, current_balance);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.make_cell_sovereign = make_cell_sovereign;

    /**
     * Match an intent against an agent's held tokens.
     * @param {number} handle
     * @param {number} intent_index
     * @param {number} agent_index
     * @returns {any}
     */
    function match_intent_for_agent(handle, intent_index, agent_index) {
        const ret = wasm.match_intent_for_agent(handle, intent_index, agent_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.match_intent_for_agent = match_intent_for_agent;

    /**
     * Generate a Merkle membership proof for a specific leaf.
     *
     * Returns JSON with the proof path and verification result.
     * @param {string} leaves_json
     * @param {string} target_leaf
     * @returns {any}
     */
    function merkle_membership_proof(leaves_json, target_leaf) {
        const ptr0 = passStringToWasm0(leaves_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(target_leaf, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.merkle_membership_proof(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.merkle_membership_proof = merkle_membership_proof;

    /**
     * Generate a non-membership proof for a leaf NOT in the set.
     * @param {string} leaves_json
     * @param {string} absent_leaf
     * @returns {any}
     */
    function merkle_non_membership_proof(leaves_json, absent_leaf) {
        const ptr0 = passStringToWasm0(leaves_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(absent_leaf, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.merkle_non_membership_proof(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.merkle_non_membership_proof = merkle_non_membership_proof;

    /**
     * Mint a new root macaroon token.
     *
     * Returns JSON: { "token": "<em2_...>", "key_hex": "<hex>" }
     * @param {Uint8Array} root_key
     * @param {string} location
     * @returns {any}
     */
    function mint_token(root_key, location) {
        const ptr0 = passArray8ToWasm0(root_key, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(location, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.mint_token(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.mint_token = mint_token;

    /**
     * **OPEN-SURFACE** — open the `owner_agent_index` agent's OWN cell as a surface
     * (a window) at `rights`, and return its live identity (the T2 badge source).
     *
     * A surface IS a cell; this confirms the cell exists, hands the owner an
     * ORIGINAL self-cap over it at `rights` (the Viewport the compositor renders),
     * and reads off the live identity. Returns the `SurfaceIdentity`
     * `{ owning_cell_id, lifecycle, source_state_root, balance, accepts_effects }`
     * drawn FROM THE LEDGER — so the JS compositor draws the badge from the live
     * cell, never the page.
     * @param {number} handle
     * @param {number} owner_agent_index
     * @param {string} rights
     * @returns {any}
     */
    function open_surface(handle, owner_agent_index, rights) {
        const ptr0 = passStringToWasm0(rights, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.open_surface(handle, owner_agent_index, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.open_surface = open_surface;

    /**
     * Prepare a peer exchange with STARK proof.
     *
     * This generates the proof payload that accompanies a direct peer-to-peer
     * state exchange between two sovereign cell owners.
     *
     * Returns JSON: { exchange_id, proof_commitment, sender_cell, receiver_cell }
     * @param {string} sender_cell_hex
     * @param {string} receiver_cell_hex
     * @param {bigint} amount
     * @returns {any}
     */
    function peer_exchange_with_proof(sender_cell_hex, receiver_cell_hex, amount) {
        const ptr0 = passStringToWasm0(sender_cell_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(receiver_cell_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.peer_exchange_with_proof(ptr0, len0, ptr1, len1, amount);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.peer_exchange_with_proof = peer_exchange_with_proof;

    /**
     * **PRESENT** — does `holder_agent_index` hold draw authority (`required`) over
     * the surface backed by `surface_owner_agent_index`'s cell?
     *
     * Resolves the surface cap against real cell-state requiring `required`
     * (`required ⊆ held`, the REAL `is_attenuation`). A read-only mirror asking for
     * a wider authority is refused. Returns a `SurfaceOutcome`
     * `{ ok, reason, revocation_immediate, commit_synchronous }`; on refusal
     * `reason` is the teaching string. (For the owner presenting into its own
     * window, pass the same index for holder and surface owner.)
     * @param {number} handle
     * @param {number} holder_agent_index
     * @param {number} surface_owner_agent_index
     * @param {string} required
     * @returns {any}
     */
    function present_surface(handle, holder_agent_index, surface_owner_agent_index, required) {
        const ptr0 = passStringToWasm0(required, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.present_surface(handle, holder_agent_index, surface_owner_agent_index, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.present_surface = present_surface;

    /**
     * **THE PRODUCER** — fold a real `k`-turn chain in the tab and emit its
     * [`ExternalHistoryEnvelope`] as JSON, with `proof_bytes_b64` populated from the
     * proof's versioned byte envelope. This is the artifact a node/relayer ships and a
     * tab feeds to [`verify_devnet_history`]; producing it in-tab makes the whole
     * round-trip (fold → serialize → bytes → deserialize → verify) tactile.
     *
     * The carried `vk_fingerprint_hex` is the producer's CLAIM (the verifier re-pins
     * from the bytes regardless). `k` is clamped to `[2, 4]` (recursive proving is
     * heavy). Returns the JSON string.
     * @param {number} k
     * @param {bigint} step
     * @returns {string}
     */
    function produce_external_history_envelope(k, step) {
        let deferred2_0;
        let deferred2_1;
        try {
            const ret = wasm.produce_external_history_envelope(k, step);
            var ptr1 = ret[0];
            var len1 = ret[1];
            if (ret[3]) {
                ptr1 = 0; len1 = 0;
                throw takeFromExternrefTable0(ret[2]);
            }
            deferred2_0 = ptr1;
            deferred2_1 = len1;
            return getStringFromWasm0(ptr1, len1);
        } finally {
            wasm.__wbindgen_free(deferred2_0, deferred2_1, 1);
        }
    }
    exports.produce_external_history_envelope = produce_external_history_envelope;

    /**
     * Submit a batch of revocation events from node 0 and immediately drive
     * a consensus round. `events_json` is a JSON array of token-id strings;
     * each becomes a `RevocationEvent` signed by node 0's signing key.
     *
     * Behavioral note vs. the deleted SimFederation: real `run_consensus_round`
     * requires the leader's `pending_events` to be non-empty AND a quorum of
     * online nodes (n - floor(n/3)) to vote — proposing with no events or with
     * too few online nodes will return `block_hash: null`.
     * @param {number} handle
     * @param {number} fed_index
     * @param {string} events_json
     * @returns {any}
     */
    function propose_block(handle, fed_index, events_json) {
        const ptr0 = passStringToWasm0(events_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.propose_block(handle, fed_index, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.propose_block = propose_block;

    /**
     * Generate a blinded ring membership proof for an agent in a set.
     *
     * Proves that an agent (identified by `agent_id_hex`) is a member of the ring
     * defined by `ring_members_json` (a JSON array of hex-encoded 32-byte IDs)
     * without revealing which specific member they are.
     *
     * `agent_id_hex`: hex-encoded 32-byte agent identity
     * `ring_members_json`: JSON array of hex-encoded 32-byte member identities
     *
     * Returns JSON with: blinded_leaf, presentation_tag, set_root, ring_size, proof_size
     * @param {string} agent_id_hex
     * @param {string} ring_members_json
     * @returns {any}
     */
    function prove_anonymous_membership(agent_id_hex, ring_members_json) {
        const ptr0 = passStringToWasm0(agent_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(ring_members_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.prove_anonymous_membership(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.prove_anonymous_membership = prove_anonymous_membership;

    /**
     * Produce (and cache) a REAL Stage 7-γ.2 cross-cell bilateral *aggregate*
     * proof — the GOLDEN tier — over a canonical two-cell transfer scenario, and
     * return its summary (including the matched outgoing/incoming transfer roots).
     *
     * This is NOT a tier flip on a single-turn EffectVM proof. It runs the
     * canonical γ.2 aggregator
     * (`dregg_turn::aggregate_bilateral_prover::prove_aggregated_bundle`) over two
     * per-cell `WitnessedReceipt`s — alice's OUTGOING transfer + bob's INCOMING
     * transfer, both projected from the SAME canonical Turn's bilateral schedule —
     * emitting a real outer STARK over `BilateralAggregationAir`. The bundle is
     * then self-verified (`verify_aggregated_bundle`: real outer-STARK
     * verification + Turn-derived cross-cell schedule re-check) BEFORE the record
     * is cached, so a returned result is a genuinely sound cross-cell aggregate —
     * never a faked tier.
     *
     * PERFORMANCE: like `prove_turn`, proving is expensive in wasm and is NOT run
     * at boot. The Proofs section calls this lazily; it is idempotent (re-proving
     * once cached is a cheap no-op).
     *
     * Returns
     * `{ kind, proof_size_bytes, n_cells, bilateral_consistent, roots_matched,
     *    outgoing_transfer_root, incoming_transfer_root, shared_transfer_id,
     *    sender_cell, receiver_cell, amount }`. `roots_matched == true` is the
     * headline GOLDEN signal: the aggregate self-verified (`bilateral_consistent`
     * + the Turn-derived schedule re-check inside `verify_aggregated_bundle`) and
     * both transfer roots are present (non-zero). The outgoing/incoming roots are
     * domain-separated and so intentionally NOT byte-equal; the cross-cell binding
     * is the `shared_transfer_id` both sides fold over, attested by the verified
     * aggregate.
     * @param {number} handle
     * @returns {any}
     */
    function prove_bilateral_aggregate(handle) {
        const ret = wasm.prove_bilateral_aggregate(handle);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.prove_bilateral_aggregate = prove_bilateral_aggregate;

    /**
     * Prove that a private value meets a committed threshold (value >= threshold)
     * without revealing either value to third parties.
     *
     * `value`: the prover's private attribute value (u32 field element)
     * `threshold`: the verifier's threshold (u32 field element)
     * `blinding`: randomness for the threshold commitment (u32 field element)
     *
     * Returns JSON with: proof bytes, threshold_commitment, fact_commitment, verified status.
     * Returns error if the predicate is not satisfiable (value < threshold).
     * @param {number} _value
     * @param {number} _threshold
     * @param {number} _blinding
     * @returns {any}
     */
    function prove_committed_threshold(_value, _threshold, _blinding) {
        const ret = wasm.prove_committed_threshold(_value, _threshold, _blinding);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.prove_committed_threshold = prove_committed_threshold;

    /**
     * Produce a **real** conservation proof for a balanced transaction.
     *
     * Given inputs and outputs (each `{ value, blinding_hex }`) plus a `message_hex`
     * binding context, this builds the real Ristretto `ValueCommitment`s, computes
     * the excess blinding `Σ input_blindings − Σ output_blindings` internally, and
     * produces the canonical `dregg_cell_crypto::ConservationProof` (Schnorr excess
     * signature). All the curve25519-dalek work happens inside `dregg_cell`
     * (`prove_conservation_bytes`); this binding only marshals bytes.
     *
     * The returned shape is EXACTLY what `verify_conservation_proof` parses:
     * ```json
     * {
     *   "input_commitments":  ["<hex32>", ...],
     *   "output_commitments": ["<hex32>", ...],
     *   "proof": { "excess_commitment": "<hex32>",
     *              "nonce_commitment":  "<hex32>",
     *              "response":          "<hex32>" },
     *   "message_hex": "<hex>"
     * }
     * ```
     *
     * Soundness note: this binding now produces the FULL conservation proof —
     * the Schnorr excess relation (value balance) AND one real Bulletproof range
     * proof per output (`[0, 2^64)`). The returned `output_range_proofs` are
     * hex-encoded serialized `bulletproofs::RangeProof`s. When fed back to
     * `verify_conservation_proof`, a `valid: true` with `range_proofs_checked:
     * true` means both "the excess balances" AND "every output is a non-negative
     * 64-bit value" — i.e. the negative-value (mod-order wrap) inflation attack is
     * ruled out. The Bulletproofs verifier runs natively on wasm32 (bulletproofs
     * v5 over curve25519-dalek compiles to wasm32-unknown-unknown).
     * @param {string} inputs_json
     * @param {string} outputs_json
     * @param {string} message_hex
     * @returns {any}
     */
    function prove_conservation(inputs_json, outputs_json, message_hex) {
        const ptr0 = passStringToWasm0(inputs_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(outputs_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(message_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ret = wasm.prove_conservation(ptr0, len0, ptr1, len1, ptr2, len2);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.prove_conservation = prove_conservation;

    /**
     * Generate (and cache) a REAL EffectVM STARK proof for a committed turn,
     * identified by its `turn_hash` (hex32).
     *
     * This drives the canonical ROTATED Effect VM prove path — the rotated
     * multi-table `Ir2BatchProof` minted over the cohort descriptor
     * (`mint_rotated_participant_leg`). The proof is self-verified before being
     * cached, so once this returns Ok the turn's `get_receipt_chain` entry carries
     * a real `proof_view` (Silver tier).
     *
     * PERFORMANCE: STARK proving is expensive in wasm, so this is NOT run on the
     * commit path or at boot. The `<dregg-proof>` inspector calls it lazily on
     * first view; it is idempotent (re-proving a cached turn is a cheap no-op),
     * so repeated inspector renders cost nothing after the first.
     *
     * Returns `{ kind, proof_size_bytes, trace_rows, net_delta }` describing the
     * generated (or already-cached) proof.
     * @param {number} handle
     * @param {string} turn_hash_hex
     * @returns {any}
     */
    function prove_turn(handle, turn_hash_hex) {
        const ptr0 = passStringToWasm0(turn_hash_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.prove_turn(handle, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.prove_turn = prove_turn;

    /**
     * Read a single 32-byte cell slot as lowercase hex (or `null` if absent).
     * @param {number} handle
     * @param {string} cell_id_hex
     * @param {number} index
     * @returns {any}
     */
    function read_cell_field(handle, cell_id_hex, index) {
        const ptr0 = passStringToWasm0(cell_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.read_cell_field(handle, ptr0, len0, index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.read_cell_field = read_cell_field;

    /**
     * Register (or record) a federation in the runtime's known set (sim).
     * committee_pubkeys_json: array of hex pubkeys (minimal: derives n).
     * Unblocks extension `registerFederation` + list in plan §4.3/§5.7.
     * @param {number} handle
     * @param {string} name
     * @param {string} committee_pubkeys_json
     * @returns {any}
     */
    function register_federation(handle, name, committee_pubkeys_json) {
        const ptr0 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(committee_pubkeys_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.register_federation(handle, ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.register_federation = register_federation;

    /**
     * Register a peer cell on the named agent's exchange session, anchoring it
     * to an initial commitment that the two parties agreed on out-of-band.
     * Must be called before `verify_peer_transition` will accept transitions
     * from that peer.
     * @param {number} handle
     * @param {number} agent_idx
     * @param {string} peer_cell_id_hex
     * @param {string} peer_pubkey_hex
     * @param {string} initial_commitment_hex
     * @returns {any}
     */
    function register_peer(handle, agent_idx, peer_cell_id_hex, peer_pubkey_hex, initial_commitment_hex) {
        const ptr0 = passStringToWasm0(peer_cell_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(peer_pubkey_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(initial_commitment_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ret = wasm.register_peer(handle, agent_idx, ptr0, len0, ptr1, len1, ptr2, len2);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.register_peer = register_peer;

    /**
     * Register a real Ed25519 threshold verifier under `vk_hash_hex` for the
     * governed-namespace `commit_table_update` flow. `committee_pubkeys_json` is a
     * JSON array of 64-char hex public keys; `threshold` is the count of distinct
     * valid committee signatures required.
     * @param {number} handle
     * @param {string} vk_hash_hex
     * @param {string} committee_pubkeys_json
     * @param {number} threshold
     * @returns {any}
     */
    function register_threshold_verifier(handle, vk_hash_hex, committee_pubkeys_json, threshold) {
        const ptr0 = passStringToWasm0(vk_hash_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(committee_pubkeys_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.register_threshold_verifier(handle, ptr0, len0, ptr1, len1, threshold);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.register_threshold_verifier = register_threshold_verifier;

    /**
     * Revoke a capability by slot.
     * @param {number} handle
     * @param {number} agent_index
     * @param {number} slot
     * @returns {any}
     */
    function revoke_capability(handle, agent_index, slot) {
        const ret = wasm.revoke_capability(handle, agent_index, slot);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.revoke_capability = revoke_capability;

    /**
     * **REVOKE-SURFACE** — drop `holder_agent_index`'s cap over the surface backed
     * by `surface_owner_agent_index`'s cell; the glass goes dark.
     *
     * At n=1 (the local tab) this is SYNCHRONOUS — the cap is dead the instant it
     * returns, and a subsequent `present_surface` finds nothing held. Returns
     * `true` iff a live surface cap was removed.
     * @param {number} handle
     * @param {number} holder_agent_index
     * @param {number} surface_owner_agent_index
     * @returns {boolean}
     */
    function revoke_surface(handle, holder_agent_index, surface_owner_agent_index) {
        const ret = wasm.revoke_surface(handle, holder_agent_index, surface_owner_agent_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return ret[0] !== 0;
    }
    exports.revoke_surface = revoke_surface;

    /**
     * Canonical route-table commitment for a governed-namespace route table.
     * `routes_json` is a JSON array of `[path, handler]` pairs. Returns the BLAKE3
     * commitment hex — the value that becomes slot 0 after a successful commit.
     * Uses `dregg_dfa::RouteTableBuilder` + `RouteTable::commitment` (canonical).
     * @param {string} routes_json
     * @returns {string}
     */
    function route_table_commitment(routes_json) {
        let deferred3_0;
        let deferred3_1;
        try {
            const ptr0 = passStringToWasm0(routes_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.route_table_commitment(ptr0, len0);
            var ptr2 = ret[0];
            var len2 = ret[1];
            if (ret[3]) {
                ptr2 = 0; len2 = 0;
                throw takeFromExternrefTable0(ret[2]);
            }
            deferred3_0 = ptr2;
            deferred3_1 = len2;
            return getStringFromWasm0(ptr2, len2);
        } finally {
            wasm.__wbindgen_free(deferred3_0, deferred3_1, 1);
        }
    }
    exports.route_table_commitment = route_table_commitment;

    /**
     * Scan a batch of stealth announcements for notes addressed to us.
     *
     * `announcements_json`: JSON array of { ephemeral_pubkey: number[], view_tag: number }
     * Returns JSON array of indices that belong to us.
     * @param {Uint8Array} view_privkey
     * @param {Uint8Array} spend_pubkey
     * @param {string} announcements_json
     * @returns {any}
     */
    function scan_stealth_announcements(view_privkey, spend_pubkey, announcements_json) {
        const ptr0 = passArray8ToWasm0(view_privkey, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(spend_pubkey, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(announcements_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ret = wasm.scan_stealth_announcements(ptr0, len0, ptr1, len1, ptr2, len2);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.scan_stealth_announcements = scan_stealth_announcements;

    /**
     * Generate a Schnorr keypair from a random seed.
     *
     * Returns JSON: { "secret_key": [8 u32 elements], "public_key": { "x": [8], "y": [8] } }
     * @returns {any}
     */
    function schnorr_keygen() {
        const ret = wasm.schnorr_keygen();
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.schnorr_keygen = schnorr_keygen;

    /**
     * Sign a message with a Schnorr secret key.
     *
     * `secret_key_json`: JSON with { "secret_key": [32 bytes] }
     * `message`: the message string to sign
     *
     * Returns JSON with signature { "r_x": [8], "r_y": [8], "s": [8] }
     * @param {string} secret_key_json
     * @param {string} message
     * @returns {any}
     */
    function schnorr_sign(secret_key_json, message) {
        const ptr0 = passStringToWasm0(secret_key_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(message, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.schnorr_sign(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.schnorr_sign = schnorr_sign;

    /**
     * Verify a Schnorr signature.
     *
     * `public_key_json`: JSON with { "public_key_x": [8 u32], "public_key_y": [8 u32] }
     * `message`: the message string
     * `signature_json`: JSON with { "r_x": [8 u32], "r_y": [8 u32], "s": [32 bytes] }
     *
     * Returns bool: true if signature is valid.
     * @param {string} public_key_json
     * @param {string} message
     * @param {string} signature_json
     * @returns {boolean}
     */
    function schnorr_verify(public_key_json, message, signature_json) {
        const ptr0 = passStringToWasm0(public_key_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(message, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(signature_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ret = wasm.schnorr_verify(ptr0, len0, ptr1, len1, ptr2, len2);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return ret[0] !== 0;
    }
    exports.schnorr_verify = schnorr_verify;

    /**
     * Seal (encrypt) an intent body for a recipient.
     *
     * A 32-byte recipient X25519 public key is **required**. The previous
     * "broadcast mode" path derived the recipient key as a deterministic BLAKE3
     * of the plaintext, which provided no confidentiality (identical plaintexts
     * produced identical ciphertexts and anyone who could guess the plaintext
     * could decrypt it). That mode has been removed.
     *
     * To send a publicly-decryptable envelope, generate a fresh ephemeral
     * X25519 keypair, encrypt to its public key, and publish the corresponding
     * private key out-of-band (or alongside the ciphertext with a clear
     * "broadcast" label).
     *
     * Returns JSON: { ciphertext, ephemeral_pubkey }
     * @param {string} plaintext_json
     * @param {Uint8Array | null} [recipient_pubkey]
     * @returns {any}
     */
    function seal_intent_body(plaintext_json, recipient_pubkey) {
        const ptr0 = passStringToWasm0(plaintext_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        var ptr1 = isLikeNone(recipient_pubkey) ? 0 : passArray8ToWasm0(recipient_pubkey, wasm.__wbindgen_malloc);
        var len1 = WASM_VECTOR_LEN;
        const ret = wasm.seal_intent_body(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.seal_intent_body = seal_intent_body;

    /**
     * **SHARE-SURFACE** — hand the window backed by `surface_owner_agent_index`'s
     * cell from `from_agent_index` to `to_agent_index`, narrowed to `narrower`, as a
     * GENUINE `Effect::GrantCapability` turn through the real executor.
     *
     * The executor enforces `granted ⊆ held`: an attenuating share commits; a
     * WIDENING share is rejected with `DelegationDenied` (the `⚠ over-share` moment
     * at the pixel layer). Returns a `SurfaceOutcome` whose `reason` carries the
     * executor's own reason on refusal.
     * @param {number} handle
     * @param {number} from_agent_index
     * @param {number} to_agent_index
     * @param {number} surface_owner_agent_index
     * @param {string} narrower
     * @returns {any}
     */
    function share_surface(handle, from_agent_index, to_agent_index, surface_owner_agent_index, narrower) {
        const ptr0 = passStringToWasm0(narrower, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.share_surface(handle, from_agent_index, to_agent_index, surface_owner_agent_index, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.share_surface = share_surface;

    /**
     * Sign the given canonical message (hex) with `signer_agent_index`'s
     * cipherclerk, returning a 96-byte `(pubkey ‖ sig)` record as hex. Concatenate
     * `threshold` such records (hex) to form the proof for
     * `execute_custom_auth_turn`.
     * @param {number} handle
     * @param {number} signer_agent_index
     * @param {string} message_hex
     * @returns {string}
     */
    function sign_custom_commit(handle, signer_agent_index, message_hex) {
        let deferred3_0;
        let deferred3_1;
        try {
            const ptr0 = passStringToWasm0(message_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.sign_custom_commit(handle, signer_agent_index, ptr0, len0);
            var ptr2 = ret[0];
            var len2 = ret[1];
            if (ret[3]) {
                ptr2 = 0; len2 = 0;
                throw takeFromExternrefTable0(ret[2]);
            }
            deferred3_0 = ptr2;
            deferred3_1 = len2;
            return getStringFromWasm0(ptr2, len2);
        } finally {
            wasm.__wbindgen_free(deferred3_0, deferred3_1, 1);
        }
    }
    exports.sign_custom_commit = sign_custom_commit;

    /**
     * Sign an arbitrary message with a 32-byte Ed25519 secret-key seed.
     *
     * Returns the 64-byte Ed25519 signature. The extension background uses this
     * to sign turn JSON when `build_turn` is unavailable (e.g., a turn type that
     * doesn't map to a canonical Effect). For canonical turn construction use
     * `build_turn` instead — it routes through `AgentCipherclerk` directly.
     *
     * `secret_key` must be exactly 32 bytes (the seed, not the full 64-byte
     * expanded key). `message` may be any length.
     *
     * Returns a `Uint8Array` of 64 signature bytes.
     * @param {Uint8Array} secret_key
     * @param {Uint8Array} message
     * @returns {Uint8Array}
     */
    function sign_message(secret_key, message) {
        const ptr0 = passArray8ToWasm0(secret_key, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(message, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.sign_message(ptr0, len0, ptr1, len1);
        if (ret[3]) {
            throw takeFromExternrefTable0(ret[2]);
        }
        var v3 = getArrayU8FromWasm0(ret[0], ret[1]).slice();
        wasm.__wbindgen_free(ret[0], ret[1] * 1, 1);
        return v3;
    }
    exports.sign_message = sign_message;

    /**
     * Sign a pre-built, encoded `Turn` via the canonical v3 signing path.
     *
     * This is the substrate behind the extension's `dregg.signTurnV3(turnBytes)`
     * surface (STARBRIDGE-PLAN §4.3 Task #28 item 5). starbridge-apps turn-builders
     * produce raw `Turn` bytes whose actions carry `Authorization::Unchecked`; this
     * function walks the call forest and replaces every `Unchecked` action with a
     * real Ed25519 signature using `AgentCipherclerk::sign_action` — the exact same
     * canonical path `DreggRuntime::execute_turn_for_agent` uses (`sign_call_forest`
     * → `cipherclerk.sign_action` → `TurnExecutor::compute_signing_message`). No
     * hand-rolled cryptography; the v3 signing message format is whatever the SDK's
     * `compute_signing_message` produces today.
     *
     * # Encoding contract (honest substrate note)
     *
     * The task spec named postcard, but `dregg_turn::Turn` carries
     * `#[serde(skip_serializing_if = ...)]` fields and postcard is NOT
     * self-describing, so `postcard::to_allocvec(&turn)` → `postcard::from_bytes::<Turn>`
     * does NOT round-trip (it fails "Hit the end of buffer"). This is a pre-existing
     * substrate asymmetry, verified directly against the `turn` crate. To stay usable
     * without faking anything, this signer accepts the turn bytes as **either**
     * postcard or self-describing JSON, tries postcard first and falls back to JSON,
     * and returns the signed turn in **both** encodings so the caller can pick the
     * one its downstream consumer accepts. JSON is the reliable round-trip form until
     * the substrate adds a postcard-safe wire encoding for `Turn`.
     *
     * Arguments (all from the extension's cipherclerk context):
     * - `turn_bytes`: encoded `Turn` (postcard or JSON) with Unchecked actions.
     * - `sender_privkey`: 32-byte Ed25519 seed (the cipherclerk's secret key).
     * - `federation_id`: 32-byte federation id the signing message binds against
     *   (all-zeros for devnet/sim genesis; the node's `local_federation_id`).
     *
     * Returns JSON: `{ turn_id, turn_bytes (postcard), turn_bytes_json (JSON),
     * encoding ("postcard"|"json"; the encoding the INPUT was decoded as),
     * signer_pubkey }`. Actions already carrying a non-`Unchecked` authorization are
     * left intact (pre-signed / pre-proven actions are preserved).
     * @param {Uint8Array} turn_bytes
     * @param {Uint8Array} sender_privkey
     * @param {Uint8Array} federation_id
     * @returns {any}
     */
    function sign_turn_v3(turn_bytes, sender_privkey, federation_id) {
        const ptr0 = passArray8ToWasm0(turn_bytes, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(sender_privkey, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passArray8ToWasm0(federation_id, wasm.__wbindgen_malloc);
        const len2 = WASM_VECTOR_LEN;
        const ret = wasm.sign_turn_v3(ptr0, len0, ptr1, len1, ptr2, len2);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.sign_turn_v3 = sign_turn_v3;

    /**
     * Drive a single consensus round on the federation without submitting new
     * events (events already in `pending_events` will be picked up). Returns
     * the finalized block summary or null if the round did not finalize.
     * @param {number} handle
     * @param {number} fed_index
     * @returns {any}
     */
    function simulate_consensus_round(handle, fed_index) {
        const ret = wasm.simulate_consensus_round(handle, fed_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.simulate_consensus_round = simulate_consensus_round;

    /**
     * Spend a note (reveal its nullifier).
     * @param {number} handle
     * @param {number} agent_index
     * @param {bigint} value
     * @param {bigint} asset_type
     * @returns {any}
     */
    function spend_note(handle, agent_index, value, asset_type) {
        const ret = wasm.spend_note(handle, agent_index, value, asset_type);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.spend_note = spend_note;

    /**
     * Submit a conditional turn (executes only when condition is proven).
     * @param {number} handle
     * @param {number} agent_index
     * @param {string} actions_json
     * @param {bigint} fee
     * @param {string} condition_json
     * @param {bigint} timeout_blocks
     * @returns {any}
     */
    function submit_conditional(handle, agent_index, actions_json, fee, condition_json, timeout_blocks) {
        const ptr0 = passStringToWasm0(actions_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(condition_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.submit_conditional(handle, agent_index, ptr0, len0, fee, ptr1, len1, timeout_blocks);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.submit_conditional = submit_conditional;

    /**
     * Does `holder_agent_index` hold a surface cap over the surface backed by
     * `surface_owner_agent_index`'s cell? (Used by the compositor to decide whether
     * to paint a recipient's pane.)
     * @param {number} handle
     * @param {number} holder_agent_index
     * @param {number} surface_owner_agent_index
     * @returns {boolean}
     */
    function surface_holds_cap(handle, holder_agent_index, surface_owner_agent_index) {
        const ret = wasm.surface_holds_cap(handle, holder_agent_index, surface_owner_agent_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return ret[0] !== 0;
    }
    exports.surface_holds_cap = surface_holds_cap;

    /**
     * **SURFACE-IDENTITY** — the anti-spoof T2 badge for the surface backed by
     * `surface_owner_agent_index`'s cell, read FROM THE LIVE LEDGER.
     *
     * Returns `{ owning_cell_id, lifecycle, source_state_root, balance,
     * accepts_effects }` — each a function of the cell's real state, never the
     * page's self-description.
     * @param {number} handle
     * @param {number} surface_owner_agent_index
     * @returns {any}
     */
    function surface_identity(handle, surface_owner_agent_index) {
        const ret = wasm.surface_identity(handle, surface_owner_agent_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.surface_identity = surface_identity;

    /**
     * The rights `holder_agent_index` holds over the surface backed by
     * `surface_owner_agent_index`'s cell, as a string (e.g. `"Signature"`,
     * `"None"`), or `null` if none. (The compositor renders the pane's CAN/CAN'T
     * chrome from this.)
     * @param {number} handle
     * @param {number} holder_agent_index
     * @param {number} surface_owner_agent_index
     * @returns {any}
     */
    function surface_rights_held(handle, holder_agent_index, surface_owner_agent_index) {
        const ret = wasm.surface_rights_held(handle, holder_agent_index, surface_owner_agent_index);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.surface_rights_held = surface_rights_held;

    /**
     * Tamper with a demo membership proof by flipping the claimed root in its
     * envelope's public inputs. The `Ir2BatchProof` still decodes, but its claim no
     * longer matches the witnessed root, so `verify_demo_stark_proof` REJECTS it --
     * demonstrating the binding between an IR-v2 proof and its public claim.
     *
     * Returns the tampered envelope JSON.
     * @param {string} proof_json
     * @returns {string}
     */
    function tamper_demo_stark_proof(proof_json) {
        let deferred3_0;
        let deferred3_1;
        try {
            const ptr0 = passStringToWasm0(proof_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
            const len0 = WASM_VECTOR_LEN;
            const ret = wasm.tamper_demo_stark_proof(ptr0, len0);
            var ptr2 = ret[0];
            var len2 = ret[1];
            if (ret[3]) {
                ptr2 = 0; len2 = 0;
                throw takeFromExternrefTable0(ret[2]);
            }
            deferred3_0 = ptr2;
            deferred3_1 = len2;
            return getStringFromWasm0(ptr2, len2);
        } finally {
            wasm.__wbindgen_free(deferred3_0, deferred3_1, 1);
        }
    }
    exports.tamper_demo_stark_proof = tamper_demo_stark_proof;

    /**
     * **AMEND** the source named `name` to `new_content` — advance the SAME `dregg://`
     * ref to a NEW finalized value at a NEW height (a verified state advance).
     *
     * The REAL [`WebOfCells::amend`]: the `dregg://` ref is UNCHANGED (Nelson's
     * unbreakable link), but it now resolves to the source's NEW committed value, with
     * a fresh serve-receipt + an advanced federation height. A subsequent LIVE read
     * follows it; a SNAPSHOT taken before stays pinned. Returns the new height.
     * @param {number} handle
     * @param {string} name
     * @param {string} new_content
     * @returns {bigint}
     */
    function transclusion_amend(handle, name, new_content) {
        const ptr0 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(new_content, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.transclusion_amend(handle, ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return BigInt.asUintN(64, ret[0]);
    }
    exports.transclusion_amend = transclusion_amend;

    /**
     * **BACKLINKS** (the two-way link, finally honest): enumerate WHO transcludes the
     * source named `name` — the reverse index [`transclusion_include_into`] populates,
     * wrapping the real [`Backlinks::observers_of`]. Each entry carries the cited
     * receipt + content commitment from the observation's provenance, so a backlink is
     * a verifiable claim ("observer O quoted source S's value V at receipt R") that a
     * third party can recheck — never a dangling pointer. Returns a
     * [`BacklinksReadout`]; a source nobody quotes yields an EMPTY readout, not an
     * error.
     * @param {number} handle
     * @param {string} name
     * @returns {any}
     */
    function transclusion_backlinks(handle, name) {
        const ptr0 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.transclusion_backlinks(handle, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.transclusion_backlinks = transclusion_backlinks;

    /**
     * **CREATE** a fresh transclusion demo world (a real [`WebOfCells`] with a 3-of-3
     * quorum) and return its handle. Mirrors `create_runtime`.
     * @returns {number}
     */
    function transclusion_create() {
        const ret = wasm.transclusion_create();
        return ret >>> 0;
    }
    exports.transclusion_create = transclusion_create;

    /**
     * **DESTROY** a demo world, freeing it. Returns true iff the handle was live.
     * @param {number} handle
     * @returns {boolean}
     */
    function transclusion_destroy(handle) {
        const ret = wasm.transclusion_destroy(handle);
        return ret !== 0;
    }
    exports.transclusion_destroy = transclusion_destroy;

    /**
     * **FORGE ATTEMPT** (the anti-ghost tooth `transclusion_forge_refused`): fetch the
     * source named `name`, then TAMPER the served bytes to `forged_content` and run the
     * genuine client-side verification.
     *
     * A lying node that swaps the bytes after the commitment is caught by hop (1) of
     * [`AttestedResource::verify`] — `blake3(bytes) != content_hash` → REFUSED with
     * [`FetchError::ContentHashMismatch`]. A forged quote cannot be opened. Returns a
     * [`ForgeView`] whose `refused` MUST be `true` (the demo asserts the polarity).
     * @param {number} handle
     * @param {string} name
     * @param {string} forged_content
     * @returns {any}
     */
    function transclusion_forge_attempt(handle, name, forged_content) {
        const ptr0 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(forged_content, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.transclusion_forge_attempt(handle, ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.transclusion_forge_attempt = transclusion_forge_attempt;

    /**
     * **INCLUDE** (the definitional bridge `transclusion_is_observed_finalized_read`):
     * transclude the source named `name` — perform the REAL `dregg://` finalized read,
     * VERIFY its provenance, and return the verified quote.
     *
     * This is [`TranscludedField::include`]: the displayed bytes ARE the source's
     * committed bytes; the citation dates them. A forged/absent/unfinalized source
     * REFUSES here (the genuine gate). Returns a [`QuoteView`].
     * @param {number} handle
     * @param {string} name
     * @returns {any}
     */
    function transclusion_include(handle, name) {
        const ptr0 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.transclusion_include(handle, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.transclusion_include = transclusion_include;

    /**
     * **INCLUDE INTO** an observing document (the two-way-link write): transclude the
     * source named `source_name` INTO the published document named `observer_name` —
     * the same verified finalized read as [`transclusion_include`], PLUS recording the
     * observation in the demo's [`Backlinks`] reverse index (the real
     * [`Backlinks::observe`]). The backlink carries the cited receipt + content
     * commitment from the quote's provenance, so "who quotes this cell" becomes a
     * verifiable fact, not Xanadu's hand-maintained pointer. Returns a [`QuoteView`].
     *
     * The observer must itself be a PUBLISHED document (it observes from its own
     * `dregg://` cell) — an unpublished observer name is a clear error, never a
     * silent default.
     * @param {number} handle
     * @param {string} observer_name
     * @param {string} source_name
     * @returns {any}
     */
    function transclusion_include_into(handle, observer_name, source_name) {
        const ptr0 = passStringToWasm0(observer_name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(source_name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.transclusion_include_into(handle, ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.transclusion_include_into = transclusion_include_into;

    /**
     * **PROJECT FOR** a viewer (the no-amplification tooth `transclusion_no_amplify`):
     * transclude the source named `name`, then project it PER-VIEWER through the REAL
     * [`Membrane`] at `viewer_rights`, with the source served under `lineage_rights`.
     *
     * A quote confers no authority over the source beyond observing the cited value:
     * the projection meets the viewer's held authority with the lineage through the
     * genuine `is_attenuation` ([`TranscludedField::project_for`]). A weaker viewer
     * receives a strictly attenuated surface; the projection CANNOT amplify. Returns a
     * [`ProjectionView`]. `*_rights` speak the real `AuthRequired` lattice
     * (`none`/`signature`/`proof`/`either`/`impossible`).
     * @param {number} handle
     * @param {string} name
     * @param {string} viewer_rights
     * @param {string} lineage_rights
     * @returns {any}
     */
    function transclusion_project_for(handle, name, viewer_rights, lineage_rights) {
        const ptr0 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(viewer_rights, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(lineage_rights, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ret = wasm.transclusion_project_for(handle, ptr0, len0, ptr1, len1, ptr2, len2);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.transclusion_project_for = transclusion_project_for;

    /**
     * **PUBLISH** a `dregg://` source document: commit `content`'s hash into a fresh
     * origin cell's real state + bind a `committed_url`, registering it under `name`.
     *
     * The REAL [`WebOfCells::publish`] — a genuine cell-state write of the content
     * commitment + a 3-of-3 quorum attestation, so the published source is a faithful
     * finalized read source (a transclusion of it will resolve + verify). Returns a
     * [`PublishView`] with the `dregg://<cell>` ref the demo renders as the link.
     * @param {number} handle
     * @param {string} name
     * @param {string} content
     * @param {string} committed_url
     * @returns {any}
     */
    function transclusion_publish(handle, name, content, committed_url) {
        const ptr0 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(content, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(committed_url, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ret = wasm.transclusion_publish(handle, ptr0, len0, ptr1, len1, ptr2, len2);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.transclusion_publish = transclusion_publish;

    /**
     * **READ LIVE** the source named `name` — re-resolve to its CURRENT finalized
     * value (the live quote follows every amend). This is a fresh
     * [`TranscludedField::include`] each call, so as the source advances the read
     * shows the new committed value. Returns a [`QuoteView`].
     *
     * (The demo distinguishes this from a pinned snapshot taken earlier in JS: the
     * LIVE read updates after `transclusion_amend`, the snapshot does not.)
     * @param {number} handle
     * @param {string} name
     * @returns {any}
     */
    function transclusion_read_live(handle, name) {
        const ptr0 = passStringToWasm0(name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.transclusion_read_live(handle, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.transclusion_read_live = transclusion_read_live;

    /**
     * Trip a revocation channel.
     * @param {number} handle
     * @param {number} revoker_agent
     * @param {string} channel_id_hex
     * @returns {any}
     */
    function trip_revocation_channel(handle, revoker_agent, channel_id_hex) {
        const ptr0 = passStringToWasm0(channel_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.trip_revocation_channel(handle, revoker_agent, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.trip_revocation_channel = trip_revocation_channel;

    /**
     * Unseal (decrypt) an encrypted intent body.
     *
     * `ciphertext` and `ephemeral_pubkey` are byte arrays.
     * `privkey` is the 32-byte secret key.
     *
     * Returns the plaintext JSON string.
     * @param {Uint8Array} ciphertext
     * @param {Uint8Array} ephemeral_pubkey
     * @param {Uint8Array} nonce
     * @param {Uint8Array} privkey
     * @returns {string}
     */
    function unseal_intent_body(ciphertext, ephemeral_pubkey, nonce, privkey) {
        let deferred6_0;
        let deferred6_1;
        try {
            const ptr0 = passArray8ToWasm0(ciphertext, wasm.__wbindgen_malloc);
            const len0 = WASM_VECTOR_LEN;
            const ptr1 = passArray8ToWasm0(ephemeral_pubkey, wasm.__wbindgen_malloc);
            const len1 = WASM_VECTOR_LEN;
            const ptr2 = passArray8ToWasm0(nonce, wasm.__wbindgen_malloc);
            const len2 = WASM_VECTOR_LEN;
            const ptr3 = passArray8ToWasm0(privkey, wasm.__wbindgen_malloc);
            const len3 = WASM_VECTOR_LEN;
            const ret = wasm.unseal_intent_body(ptr0, len0, ptr1, len1, ptr2, len2, ptr3, len3);
            var ptr5 = ret[0];
            var len5 = ret[1];
            if (ret[3]) {
                ptr5 = 0; len5 = 0;
                throw takeFromExternrefTable0(ret[2]);
            }
            deferred6_0 = ptr5;
            deferred6_1 = len5;
            return getStringFromWasm0(ptr5, len5);
        } finally {
            wasm.__wbindgen_free(deferred6_0, deferred6_1, 1);
        }
    }
    exports.unseal_intent_body = unseal_intent_body;

    /**
     * Verify a bearer capability proof.
     *
     * Decodes the 64-byte Ed25519 signature from `bearer_token_hex`, recomputes
     * the binding from the claimed parameters, and checks the signature against
     * `delegator_pubkey_hex`.
     *
     * Returns JSON: `{ valid: bool, signature_valid: bool, expired: bool }`
     * @param {string} bearer_token_hex
     * @param {string} delegator_pubkey_hex
     * @param {string} target_cell_hex
     * @param {string} action_name
     * @param {bigint} expiry
     * @param {bigint} current_time
     * @returns {any}
     */
    function verify_bearer_cap(bearer_token_hex, delegator_pubkey_hex, target_cell_hex, action_name, expiry, current_time) {
        const ptr0 = passStringToWasm0(bearer_token_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(delegator_pubkey_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(target_cell_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ptr3 = passStringToWasm0(action_name, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len3 = WASM_VECTOR_LEN;
        const ret = wasm.verify_bearer_cap(ptr0, len0, ptr1, len1, ptr2, len2, ptr3, len3, expiry, current_time);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_bearer_cap = verify_bearer_cap;

    /**
     * Cryptographic verification of a real BearerCapProof for the inspector's
     * paste-and-verify UX. Handles BOTH delegation variants:
     * - `SignedDelegation`: verifies the delegator's Ed25519 signature over the
     *   canonical delegation message.
     * - `StarkDelegation`: verifies the STARK proof's *scope binding* — it
     *   deserializes the proof and requires its committed public inputs to equal
     *   the canonical scope vector (root issuer ‖ target ‖ scope-hash of
     *   federation/permission/expiry). This is the same Ledger-free core the
     *   in-ledger executor runs (`dregg_turn::action::verify_stark_delegation_binding`).
     *
     * Does *not* perform the full executor cap-lookup / revocation / amplification
     * checks (those require a Ledger snapshot). Accepts the canonical JSON shape of
     * BearerCapProof (or a minimal subset for the SignedDelegation sig fields).
     * Returns { delegation_kind, signature_valid, expired, valid_for_sig, binding_error? }.
     * @param {string} proof_json
     * @param {bigint} current_time
     * @param {string} federation_id_hex
     * @returns {any}
     */
    function verify_bearer_cap_proof_sig(proof_json, current_time, federation_id_hex) {
        const ptr0 = passStringToWasm0(proof_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(federation_id_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.verify_bearer_cap_proof_sig(ptr0, len0, current_time, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_bearer_cap_proof_sig = verify_bearer_cap_proof_sig;

    /**
     * Verify a committed threshold proof given the public commitments.
     *
     * `threshold_commitment`: the Poseidon2(threshold, blinding) value
     * `fact_commitment`: the binding to token state
     * `proof_json`: serialized STARK proof (from prove_committed_threshold)
     *
     * Returns JSON: { "valid": bool, "verification_time_ms": f64 }
     * @param {string} _proof_json
     * @param {number} _threshold_commitment
     * @param {number} _fact_commitment
     * @returns {any}
     */
    function verify_committed_threshold(_proof_json, _threshold_commitment, _fact_commitment) {
        const ptr0 = passStringToWasm0(_proof_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.verify_committed_threshold(ptr0, len0, _threshold_commitment, _fact_commitment);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_committed_threshold = verify_committed_threshold;

    /**
     * Verify a conservation proof (sum of inputs == sum of outputs) using the
     * canonical Pedersen/Ristretto homomorphic check from
     * `dregg_cell_crypto::value_commitment`.
     *
     * This is the SAME primitive the executor uses for committed-value turns
     * (`verify_conservation` — a Schnorr signature proving the excess
     * `Σ inputs − Σ outputs` is a commitment to *zero value*, i.e. the values
     * balance and no inflation occurred).
     *
     * # Arguments
     *
     * - `input_commitments_json`: JSON array of hex-encoded 32-byte **compressed
     *   Ristretto** value commitments (as produced by
     *   `ValueCommitment::to_bytes` / the SDK committed-turn builder).
     * - `output_commitments_json`: same format, for the created notes.
     * - `proof_json`: JSON object `{ excess_commitment, nonce_commitment,
     *   response }`, each a hex-encoded 32 bytes — the canonical
     *   `dregg_cell_crypto::ConservationProof` (Schnorr excess signature). This is the
     *   `conservation` field of the SDK's `FullConservationProof`.
     * - `message_hex`: hex-encoded binding context (e.g. the turn hash). Pass an
     *   empty string for an unbound proof. MUST match the message the prover
     *   signed or verification fails closed.
     *
     * - `output_range_proofs_json` (OPTIONAL): pass `null`/`undefined` to verify
     *   the Schnorr excess relation only (`range_proofs_checked: false`). Pass a
     *   JSON array of hex-encoded serialized Bulletproof range proofs (one per
     *   output, same order as `output_commitments`, exactly as produced by
     *   `prove_conservation`'s `output_range_proofs`) to additionally verify that
     *   every output is a non-negative 64-bit value. When present and valid,
     *   `range_proofs_checked` is `true`.
     *
     * # Soundness / fail-closed
     *
     * When `output_range_proofs_json` is provided, this binding verifies the FULL
     * conservation proof: the Schnorr excess relation (value balance) AND a real
     * per-output Bulletproof range proof (`[0, 2^64)`), via
     * `dregg_cell_crypto::value_commitment::verify_full_conservation_bytes`. A `valid:
     * true` with `range_proofs_checked: true` therefore rules out the
     * negative-value (mod-order wrap) inflation attack. The Bulletproofs verifier
     * runs natively on wasm32 (bulletproofs v5 over curve25519-dalek).
     *
     * When omitted, it verifies ONLY the Schnorr excess relation and surfaces
     * `range_proofs_checked: false` — `valid: true` then means "the excess
     * balances", not "every output is non-negative".
     *
     * Any malformed point, non-canonical scalar, message mismatch, wrong range
     * proof count, malformed/out-of-range Bulletproof, or unbalanced excess yields
     * `valid: false` with a precise `error` (never a thrown JsError).
     *
     * Returns JSON: `{ valid, range_proofs_checked, input_count, output_count,
     * error }`.
     * @param {string} input_commitments_json
     * @param {string} output_commitments_json
     * @param {string} proof_json
     * @param {string} message_hex
     * @param {string | null} [output_range_proofs_json]
     * @returns {any}
     */
    function verify_conservation_proof(input_commitments_json, output_commitments_json, proof_json, message_hex, output_range_proofs_json) {
        const ptr0 = passStringToWasm0(input_commitments_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(output_commitments_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(proof_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ptr3 = passStringToWasm0(message_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len3 = WASM_VECTOR_LEN;
        var ptr4 = isLikeNone(output_range_proofs_json) ? 0 : passStringToWasm0(output_range_proofs_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        var len4 = WASM_VECTOR_LEN;
        const ret = wasm.verify_conservation_proof(ptr0, len0, ptr1, len1, ptr2, len2, ptr3, len3, ptr4, len4);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_conservation_proof = verify_conservation_proof;

    /**
     * Verifies an `Ir2ProofEnvelope` produced by `generate_demo_stark_proof`
     * through the migrated CONSUMER contract: fail-closed `descriptor_by_name`
     * dispatch on the envelope's name, postcard-decode the `Ir2BatchProof`, and
     * check it with the deployed `verify_vm_descriptor2`. A dispatch miss, a
     * malformed blob, or a failed cryptographic check all yield `valid: false`.
     *
     * Returns JSON: { "valid": bool, "error": null | "..." }
     * @param {string} proof_json
     * @returns {any}
     */
    function verify_demo_stark_proof(proof_json) {
        const ptr0 = passStringToWasm0(proof_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.verify_demo_stark_proof(ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_demo_stark_proof = verify_demo_stark_proof;

    /**
     * **VERIFY AN EXTERNAL HISTORY against a config-pinned VK anchor** — the real
     * remote-verifier shape, over the versioned [`ExternalHistoryEnvelope`].
     *
     * In the production shape the aggregate is produced by whoever ran the history
     * (a node, a relayer), serialized into the envelope, fetched by the tab, and
     * verified against the client's genesis/checkpoint VK anchor — which arrives as a
     * SEPARATE argument (`config_anchor_hex`) and is NEVER read off the envelope under
     * verification (the light-client invariant).
     *
     * What this enforces (real, not faked):
     * 1. parse + version-check the envelope;
     * 2. parse the SEPARATE `config_anchor_hex` (the client's own configured anchor);
     * 3. the **anchor-discipline pre-check**: the envelope's claimed fingerprint is
     *    compared to the configured anchor — a mismatch is REFUSED here (the precise
     *    "this aggregate was built for a different circuit than your config pins"
     *    diagnostic), and the claimed value is otherwise discarded, never trusted;
     * 4. base64-decode `proof_bytes`, decode the inner byte envelope, and run the
     *    REAL recursion verify (the three teeth) against the config anchor — a
     *    tampered proof, a foreign circuit, or a relabeled public is refused.
     *
     * THE BYTE PATH (closed): `proof_bytes_b64` carries the base64 of the proof's
     * versioned byte envelope ([`dregg_circuit_prove::ivc_turn_chain::WholeChainProofBytes`]),
     * produced by [`produce_external_history_envelope`]. The whole [`WholeChainProof`]
     * is not byte-encodable — its `root.1` (`Rc<CircuitProverData>`) is prover-only —
     * but the VERIFY-sufficient subset (the root `BatchStarkProof`, the binding
     * `Proof`, the four publics) IS, and the verifier never reads `root.1`. So this
     * entry decodes the bytes and runs the REAL recursion verify over the wire via
     * [`dregg_lightclient::verify_history_bytes`], re-witnessing nothing.
     * @param {string} envelope_json
     * @param {string} config_anchor_hex
     * @returns {any}
     */
    function verify_devnet_history(envelope_json, config_anchor_hex) {
        const ptr0 = passStringToWasm0(envelope_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(config_anchor_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.verify_devnet_history(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_devnet_history = verify_devnet_history;

    /**
     * **LC-3 — THE FINALIZED OVER-WIRE LIGHT-CLIENT CHECK.** The same byte-path verify as
     * [`verify_devnet_history`] (legs 1+2: the aggregate is genuine, the publics are re-attested),
     * PLUS the THIRD leg — finality — that the bare wasm client lacked: the head root the aggregate
     * proves was QUORUM-FINALIZED by the client's TRUSTED committee.
     *
     * Without this leg a *correct-looking* history is indistinguishable from a *finalized* one: an
     * equivocating prover can fold a perfectly valid aggregate over a FORK the network never finalized
     * (legs 1+2 pass). This entry runs the Rust embodiment of
     * `FinalizedLightClient.light_client_accepts_finalized_history`'s third leg over the wire — the
     * composition `verify_finalized_history` performs, realized for the byte path where the in-memory
     * `WholeChainProof` is unavailable (only its publics are, which tooth 2 just re-attested):
     *
     * 1. byte-verify the aggregate against the CONFIG anchor (legs 1+2, exactly [`verify_devnet_history`]);
     * 2. the **root seam**: the envelope's finality cert finalizes the SAME head felt the aggregate proves;
     * 3. the **committee-anchored quorum**: a supermajority of the TRUSTED `committee_hex_csv` (the
     *    client's CONFIG validator set — a separate argument, NEVER read from the envelope) cast a
     *    verifying Ed25519 vote over the head root. The threshold is taken over the committee size, not
     *    the cert-supplied `participant_count` — closing red-team LC-2/LC-3.
     *
     * `committee_hex_csv` is a comma-separated list of 64-hex ed25519 validator keys.
     * `ml_dsa_committee_hex_csv` is the PARALLEL comma-separated list of the committee's genesis-ENROLLED
     * ML-DSA-65 (FIPS 204) public keys (3904 hex chars / 1952 bytes each), aligned index-for-index with
     * `committee_hex_csv` and sourced from the SAME genesis/epoch config — the GAP #0 pin's enrolled PQ
     * roster (NEVER the votes' self-carried keys). Pass an EMPTY string for the staged-rollout
     * fail-closed case: an absent or misaligned roster counts NO signer, so leg 3 refuses the hybrid
     * quorum (a refusal, never a silent ed25519-only downgrade). An empty committee, a missing finality
     * cert, a seam break, or a sub-quorum (e.g. a fork signed by foreign keys) all yield
     * `attested: false` with the precise reason — NO finalized attestation is laundered.
     * @param {string} envelope_json
     * @param {string} config_anchor_hex
     * @param {string} committee_hex_csv
     * @param {string} ml_dsa_committee_hex_csv
     * @returns {any}
     */
    function verify_finalized_devnet_history(envelope_json, config_anchor_hex, committee_hex_csv, ml_dsa_committee_hex_csv) {
        const ptr0 = passStringToWasm0(envelope_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(config_anchor_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(committee_hex_csv, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ptr3 = passStringToWasm0(ml_dsa_committee_hex_csv, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len3 = WASM_VECTOR_LEN;
        const ret = wasm.verify_finalized_devnet_history(ptr0, len0, ptr1, len1, ptr2, len2, ptr3, len3);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_finalized_devnet_history = verify_finalized_devnet_history;

    /**
     * **THE CONFIG-NOT-ARTIFACT TOOTH** — fold a real chain, then run the REAL
     * [`dregg_lightclient::verify_history`] against a VK anchor SUPPLIED BY THE
     * CALLER (the config), never self-anchored from the artifact.
     *
     * This is the in-tab realization of the light-client invariant: the trust anchor
     * is genesis/checkpoint CONFIGURATION, read from `anchor_hex` (a separate input
     * the user controls), and is NEVER taken from `agg.root_vk_fingerprint()`. The
     * REAL `verify_history` runs its three teeth (the VK pin against `anchor_hex`,
     * the carried-publics attestation against the binding proof, the root verify) —
     * re-witnessing nothing.
     *
     * - A CORRECT config anchor (e.g. from [`genesis_vk_anchor`] of the same shape)
     *   → `attested: true`, the genuine whole-history verdict.
     * - A TAMPERED/wrong anchor → `attested: false` with the genuine
     *   `VkFingerprintMismatch` reason in `named_floor` (the engine REFUSING to trust
     *   a proof of a DIFFERENT circuit) — "you did not trust the server, you CHECKED
     *   it against your own anchor."
     *
     * `anchor_hex` must be 64 hex chars (32 bytes). `k` is clamped to `[2, 4]`.
     * @param {number} k
     * @param {bigint} step
     * @param {string} anchor_hex
     * @returns {any}
     */
    function verify_history_against_anchor(k, step, anchor_hex) {
        const ptr0 = passStringToWasm0(anchor_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.verify_history_against_anchor(k, step, ptr0, len0);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_history_against_anchor = verify_history_against_anchor;

    /**
     * Postcard-decode a peer transition's bytes and verify it against the
     * named agent's exchange session. On success returns the updated
     * `PeerCellView` shape (with hex-encoded commitment + sequence +
     * last-updated). On rejection returns a `JsError` whose message includes
     * the typed variant name (e.g. `"InvalidSignature: invalid Ed25519
     * signature"`) so the UI can switch on the code.
     * @param {number} handle
     * @param {number} agent_idx
     * @param {Uint8Array} transition_bytes
     * @param {string} peer_pubkey_hex
     * @returns {any}
     */
    function verify_peer_transition(handle, agent_idx, transition_bytes, peer_pubkey_hex) {
        const ptr0 = passArray8ToWasm0(transition_bytes, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(peer_pubkey_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.verify_peer_transition(handle, agent_idx, ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_peer_transition = verify_peer_transition;

    /**
     * Verify a predicate proof.
     *
     * `proof_json`: The serialized proof (from generate_predicate_proof).
     * `threshold`: The expected threshold.
     * `fact_commitment`: The expected fact commitment (from generate_predicate_proof output).
     *
     * Returns JSON: { "valid": bool, "error": null | "..." }
     * @param {string} proof_json
     * @param {number} threshold
     * @param {number} fact_commitment
     * @returns {any}
     */
    function verify_predicate_proof(proof_json, threshold, fact_commitment) {
        const ptr0 = passStringToWasm0(proof_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ret = wasm.verify_predicate_proof(ptr0, len0, threshold, fact_commitment);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_predicate_proof = verify_predicate_proof;

    /**
     * Verify the provenance of a cell — check if it was created by a known factory.
     *
     * `cell_vk_hex`: the cell's verification key hash
     * `factory_vks_json`: JSON array of hex-encoded factory VK hashes
     *
     * Returns JSON: { from_factory: bool, factory_vk: string | null }
     * @param {string} cell_vk_hex
     * @param {string} factory_vks_json
     * @returns {any}
     */
    function verify_provenance(cell_vk_hex, factory_vks_json) {
        const ptr0 = passStringToWasm0(cell_vk_hex, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(factory_vks_json, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.verify_provenance(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_provenance = verify_provenance;

    /**
     * Verify a **real** Bulletproof range proof against a Pedersen commitment.
     *
     * `commitment`: 32-byte compressed Ristretto commitment (as produced by
     * `generate_range_proof` / `create_value_commitment`). `range_proof`: the
     * serialized Bulletproof bytes. Returns `{ valid: bool, error: string | null }`.
     * Fails closed (valid:false) on a non-point commitment or a malformed /
     * out-of-range proof — never throws for a verification failure.
     * @param {Uint8Array} commitment
     * @param {Uint8Array} range_proof
     * @returns {any}
     */
    function verify_range_proof(commitment, range_proof) {
        const ptr0 = passArray8ToWasm0(commitment, wasm.__wbindgen_malloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(range_proof, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.verify_range_proof(ptr0, len0, ptr1, len1);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_range_proof = verify_range_proof;

    /**
     * **VERIFY A PER-SLOT HEAP OPENING** — prove a rendered field VALUE equals the
     * value committed at its slot `(coll, key)` in the cell's umem heap, against the
     * cell's committed `root`, re-witnessing nothing.
     *
     * Reproduces the canonical heap path fold (`dregg_circuit::heap_root`): the leaf is
     * the arity-2 Poseidon2 digest `hash[heap_addr(coll, key), value]`; it folds up a
     * depth-`HEAP_TREE_DEPTH` tree against `siblings_csv` per `directions_csv` (bit `0`
     * = the running node is the left child → `hash_fact(cur, sib)`; `1` = right →
     * `hash_fact(sib, cur)`), and the recomputed root must equal `root`.
     *
     * All field elements are decimal `BabyBear` felts (`< 2^31`): `root`/`value`/each
     * sibling. `siblings_csv` and `directions_csv` are comma-separated, each of length
     * exactly `HEAP_TREE_DEPTH` (16) — a wrong length is REFUSED (fail-closed). A
     * tampered value, a wrong `(coll, key)`, or a forged path recomputes a different
     * root and returns `false`.
     * @param {number} root
     * @param {number} coll
     * @param {number} key
     * @param {number} value
     * @param {string} siblings_csv
     * @param {string} directions_csv
     * @returns {boolean}
     */
    function verify_slot_opening(root, coll, key, value, siblings_csv, directions_csv) {
        const ptr0 = passStringToWasm0(siblings_csv, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passStringToWasm0(directions_csv, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len1 = WASM_VECTOR_LEN;
        const ret = wasm.verify_slot_opening(root, coll, key, value, ptr0, len0, ptr1, len1);
        return ret !== 0;
    }
    exports.verify_slot_opening = verify_slot_opening;

    /**
     * Verify a macaroon token against a request.
     *
     * Returns JSON: { "allowed": bool, "policy": "...", "error": null | "..." }
     * @param {string} token_str
     * @param {Uint8Array} root_key
     * @param {string} app_id
     * @param {string} action
     * @returns {any}
     */
    function verify_token(token_str, root_key, app_id, action) {
        const ptr0 = passStringToWasm0(token_str, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len0 = WASM_VECTOR_LEN;
        const ptr1 = passArray8ToWasm0(root_key, wasm.__wbindgen_malloc);
        const len1 = WASM_VECTOR_LEN;
        const ptr2 = passStringToWasm0(app_id, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len2 = WASM_VECTOR_LEN;
        const ptr3 = passStringToWasm0(action, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
        const len3 = WASM_VECTOR_LEN;
        const ret = wasm.verify_token(ptr0, len0, ptr1, len1, ptr2, len2, ptr3, len3);
        if (ret[2]) {
            throw takeFromExternrefTable0(ret[1]);
        }
        return takeFromExternrefTable0(ret[0]);
    }
    exports.verify_token = verify_token;
    const import1 = { performance_now: function() {
  return performance.now();
} };

    function __wbg_get_imports() {
        const import0 = {
            __proto__: null,
            __wbg_Error_fdd633d4bb5dd76a: function(arg0, arg1) {
                const ret = Error(getStringFromWasm0(arg0, arg1));
                return ret;
            },
            __wbg_Number_c4bdf66bb78f7977: function(arg0) {
                const ret = Number(arg0);
                return ret;
            },
            __wbg_String_8564e559799eccda: function(arg0, arg1) {
                const ret = String(arg1);
                const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
                const len1 = WASM_VECTOR_LEN;
                getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
                getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
            },
            __wbg___wbindgen_debug_string_8a447059637473e2: function(arg0, arg1) {
                const ret = debugString(arg1);
                const ptr1 = passStringToWasm0(ret, wasm.__wbindgen_malloc, wasm.__wbindgen_realloc);
                const len1 = WASM_VECTOR_LEN;
                getDataViewMemory0().setInt32(arg0 + 4 * 1, len1, true);
                getDataViewMemory0().setInt32(arg0 + 4 * 0, ptr1, true);
            },
            __wbg___wbindgen_is_function_acc5528be2b923f2: function(arg0) {
                const ret = typeof(arg0) === 'function';
                return ret;
            },
            __wbg___wbindgen_is_object_0beba4a1980d3eea: function(arg0) {
                const val = arg0;
                const ret = typeof(val) === 'object' && val !== null;
                return ret;
            },
            __wbg___wbindgen_is_string_1fca8072260dd261: function(arg0) {
                const ret = typeof(arg0) === 'string';
                return ret;
            },
            __wbg___wbindgen_is_undefined_721f8decd50c87a3: function(arg0) {
                const ret = arg0 === undefined;
                return ret;
            },
            __wbg___wbindgen_throw_ea4887a5f8f9a9db: function(arg0, arg1) {
                throw new Error(getStringFromWasm0(arg0, arg1));
            },
            __wbg_call_5575218572ead796: function() { return handleError(function (arg0, arg1, arg2) {
                const ret = arg0.call(arg1, arg2);
                return ret;
            }, arguments); },
            __wbg_crypto_38df2bab126b63dc: function(arg0) {
                const ret = arg0.crypto;
                return ret;
            },
            __wbg_getRandomValues_3f44b700395062e5: function() { return handleError(function (arg0, arg1) {
                globalThis.crypto.getRandomValues(getArrayU8FromWasm0(arg0, arg1));
            }, arguments); },
            __wbg_getRandomValues_c44a50d8cfdaebeb: function() { return handleError(function (arg0, arg1) {
                arg0.getRandomValues(arg1);
            }, arguments); },
            __wbg_instanceof_Window_0d356b88a2f77c42: function(arg0) {
                let result;
                try {
                    result = arg0 instanceof Window;
                } catch (_) {
                    result = false;
                }
                const ret = result;
                return ret;
            },
            __wbg_length_589238bdcf171f0e: function(arg0) {
                const ret = arg0.length;
                return ret;
            },
            __wbg_msCrypto_bd5a034af96bcba6: function(arg0) {
                const ret = arg0.msCrypto;
                return ret;
            },
            __wbg_new_2e117a478906f062: function() {
                const ret = new Object();
                return ret;
            },
            __wbg_new_3444eb7412549f0b: function() {
                const ret = new Map();
                return ret;
            },
            __wbg_new_36e147a8ced3c6e0: function() {
                const ret = new Array();
                return ret;
            },
            __wbg_new_with_length_9b650f44b5c44a4e: function(arg0) {
                const ret = new Uint8Array(arg0 >>> 0);
                return ret;
            },
            __wbg_node_84ea875411254db1: function(arg0) {
                const ret = arg0.node;
                return ret;
            },
            __wbg_now_0f628e0e435c541b: function(arg0) {
                const ret = arg0.now();
                return ret;
            },
            __wbg_now_d2e0afbad4edbe82: function() {
                const ret = Date.now();
                return ret;
            },
            __wbg_now_e7c6795a7f81e10f: function(arg0) {
                const ret = arg0.now();
                return ret;
            },
            __wbg_performance_3fcf6e32a7e1ed0a: function(arg0) {
                const ret = arg0.performance;
                return ret;
            },
            __wbg_performance_4c23a97261596fec: function(arg0) {
                const ret = arg0.performance;
                return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
            },
            __wbg_process_44c7a14e11e9f69e: function(arg0) {
                const ret = arg0.process;
                return ret;
            },
            __wbg_prototypesetcall_d721637c7ca66eb8: function(arg0, arg1, arg2) {
                Uint8Array.prototype.set.call(getArrayU8FromWasm0(arg0, arg1), arg2);
            },
            __wbg_randomFillSync_6c25eac9869eb53c: function() { return handleError(function (arg0, arg1) {
                arg0.randomFillSync(arg1);
            }, arguments); },
            __wbg_require_b4edbdcf3e2a1ef0: function() { return handleError(function () {
                const ret = module.require;
                return ret;
            }, arguments); },
            __wbg_set_6be42768c690e380: function(arg0, arg1, arg2) {
                arg0[arg1] = arg2;
            },
            __wbg_set_9a1d61e17de7054c: function(arg0, arg1, arg2) {
                const ret = arg0.set(arg1, arg2);
                return ret;
            },
            __wbg_set_dc601f4a69da0bc2: function(arg0, arg1, arg2) {
                arg0[arg1 >>> 0] = arg2;
            },
            __wbg_static_accessor_GLOBAL_THIS_2fee5048bcca5938: function() {
                const ret = typeof globalThis === 'undefined' ? null : globalThis;
                return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
            },
            __wbg_static_accessor_GLOBAL_ce44e66a4935da8c: function() {
                const ret = typeof global === 'undefined' ? null : global;
                return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
            },
            __wbg_static_accessor_SELF_44f6e0cb5e67cdad: function() {
                const ret = typeof self === 'undefined' ? null : self;
                return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
            },
            __wbg_static_accessor_WINDOW_168f178805d978fe: function() {
                const ret = typeof window === 'undefined' ? null : window;
                return isLikeNone(ret) ? 0 : addToExternrefTable0(ret);
            },
            __wbg_subarray_b0e8ac4ed313fea8: function(arg0, arg1, arg2) {
                const ret = arg0.subarray(arg1 >>> 0, arg2 >>> 0);
                return ret;
            },
            __wbg_versions_276b2795b1c6a219: function(arg0) {
                const ret = arg0.versions;
                return ret;
            },
            __wbindgen_cast_0000000000000001: function(arg0) {
                // Cast intrinsic for `F64 -> Externref`.
                const ret = arg0;
                return ret;
            },
            __wbindgen_cast_0000000000000002: function(arg0) {
                // Cast intrinsic for `I64 -> Externref`.
                const ret = arg0;
                return ret;
            },
            __wbindgen_cast_0000000000000003: function(arg0, arg1) {
                // Cast intrinsic for `Ref(Slice(U8)) -> NamedExternref("Uint8Array")`.
                const ret = getArrayU8FromWasm0(arg0, arg1);
                return ret;
            },
            __wbindgen_cast_0000000000000004: function(arg0, arg1) {
                // Cast intrinsic for `Ref(String) -> Externref`.
                const ret = getStringFromWasm0(arg0, arg1);
                return ret;
            },
            __wbindgen_cast_0000000000000005: function(arg0) {
                // Cast intrinsic for `U64 -> Externref`.
                const ret = BigInt.asUintN(64, arg0);
                return ret;
            },
            __wbindgen_init_externref_table: function() {
                const table = wasm.__wbindgen_externrefs;
                const offset = table.grow(4);
                table.set(0, undefined);
                table.set(offset + 0, undefined);
                table.set(offset + 1, null);
                table.set(offset + 2, true);
                table.set(offset + 3, false);
            },
        };
        return {
            __proto__: null,
            "./dregg_wasm_bg.js": import0,
            "./snippets/biscuit-auth-314ca57174ae0e6d/inline0.js": import1,
        };
    }

    const CardWorldFinalization = (typeof FinalizationRegistry === 'undefined')
        ? { register: () => {}, unregister: () => {} }
        : new FinalizationRegistry(ptr => wasm.__wbg_cardworld_free(ptr, 1));
    const DocCollabWorldFinalization = (typeof FinalizationRegistry === 'undefined')
        ? { register: () => {}, unregister: () => {} }
        : new FinalizationRegistry(ptr => wasm.__wbg_doccollabworld_free(ptr, 1));
    const InspectorWorldFinalization = (typeof FinalizationRegistry === 'undefined')
        ? { register: () => {}, unregister: () => {} }
        : new FinalizationRegistry(ptr => wasm.__wbg_inspectorworld_free(ptr, 1));
    const KvStoreWorldFinalization = (typeof FinalizationRegistry === 'undefined')
        ? { register: () => {}, unregister: () => {} }
        : new FinalizationRegistry(ptr => wasm.__wbg_kvstoreworld_free(ptr, 1));
    const PollWorldFinalization = (typeof FinalizationRegistry === 'undefined')
        ? { register: () => {}, unregister: () => {} }
        : new FinalizationRegistry(ptr => wasm.__wbg_pollworld_free(ptr, 1));
    const TallyWorldFinalization = (typeof FinalizationRegistry === 'undefined')
        ? { register: () => {}, unregister: () => {} }
        : new FinalizationRegistry(ptr => wasm.__wbg_tallyworld_free(ptr, 1));

    function addToExternrefTable0(obj) {
        const idx = wasm.__externref_table_alloc();
        wasm.__wbindgen_externrefs.set(idx, obj);
        return idx;
    }

    function debugString(val) {
        // primitive types
        const type = typeof val;
        if (type == 'number' || type == 'boolean' || val == null) {
            return  `${val}`;
        }
        if (type == 'string') {
            return `"${val}"`;
        }
        if (type == 'symbol') {
            const description = val.description;
            if (description == null) {
                return 'Symbol';
            } else {
                return `Symbol(${description})`;
            }
        }
        if (type == 'function') {
            const name = val.name;
            if (typeof name == 'string' && name.length > 0) {
                return `Function(${name})`;
            } else {
                return 'Function';
            }
        }
        // objects
        if (Array.isArray(val)) {
            const length = val.length;
            let debug = '[';
            if (length > 0) {
                debug += debugString(val[0]);
            }
            for(let i = 1; i < length; i++) {
                debug += ', ' + debugString(val[i]);
            }
            debug += ']';
            return debug;
        }
        // Test for built-in
        const builtInMatches = /\[object ([^\]]+)\]/.exec(toString.call(val));
        let className;
        if (builtInMatches && builtInMatches.length > 1) {
            className = builtInMatches[1];
        } else {
            // Failed to match the standard '[object ClassName]'
            return toString.call(val);
        }
        if (className == 'Object') {
            // we're a user defined class or Object
            // JSON.stringify avoids problems with cycles, and is generally much
            // easier than looping through ownProperties of `val`.
            try {
                return 'Object(' + JSON.stringify(val) + ')';
            } catch (_) {
                return 'Object';
            }
        }
        // errors
        if (val instanceof Error) {
            return `${val.name}: ${val.message}\n${val.stack}`;
        }
        // TODO we could test for more things here, like `Set`s and `Map`s.
        return className;
    }

    function getArrayU8FromWasm0(ptr, len) {
        ptr = ptr >>> 0;
        return getUint8ArrayMemory0().subarray(ptr / 1, ptr / 1 + len);
    }

    let cachedBigUint64ArrayMemory0 = null;
    function getBigUint64ArrayMemory0() {
        if (cachedBigUint64ArrayMemory0 === null || cachedBigUint64ArrayMemory0.byteLength === 0) {
            cachedBigUint64ArrayMemory0 = new BigUint64Array(wasm.memory.buffer);
        }
        return cachedBigUint64ArrayMemory0;
    }

    let cachedDataViewMemory0 = null;
    function getDataViewMemory0() {
        if (cachedDataViewMemory0 === null || cachedDataViewMemory0.buffer.detached === true || (cachedDataViewMemory0.buffer.detached === undefined && cachedDataViewMemory0.buffer !== wasm.memory.buffer)) {
            cachedDataViewMemory0 = new DataView(wasm.memory.buffer);
        }
        return cachedDataViewMemory0;
    }

    function getStringFromWasm0(ptr, len) {
        return decodeText(ptr >>> 0, len);
    }

    let cachedUint8ArrayMemory0 = null;
    function getUint8ArrayMemory0() {
        if (cachedUint8ArrayMemory0 === null || cachedUint8ArrayMemory0.byteLength === 0) {
            cachedUint8ArrayMemory0 = new Uint8Array(wasm.memory.buffer);
        }
        return cachedUint8ArrayMemory0;
    }

    function handleError(f, args) {
        try {
            return f.apply(this, args);
        } catch (e) {
            const idx = addToExternrefTable0(e);
            wasm.__wbindgen_exn_store(idx);
        }
    }

    function isLikeNone(x) {
        return x === undefined || x === null;
    }

    function passArray64ToWasm0(arg, malloc) {
        const ptr = malloc(arg.length * 8, 8) >>> 0;
        getBigUint64ArrayMemory0().set(arg, ptr / 8);
        WASM_VECTOR_LEN = arg.length;
        return ptr;
    }

    function passArray8ToWasm0(arg, malloc) {
        const ptr = malloc(arg.length * 1, 1) >>> 0;
        getUint8ArrayMemory0().set(arg, ptr / 1);
        WASM_VECTOR_LEN = arg.length;
        return ptr;
    }

    function passStringToWasm0(arg, malloc, realloc) {
        if (realloc === undefined) {
            const buf = cachedTextEncoder.encode(arg);
            const ptr = malloc(buf.length, 1) >>> 0;
            getUint8ArrayMemory0().subarray(ptr, ptr + buf.length).set(buf);
            WASM_VECTOR_LEN = buf.length;
            return ptr;
        }

        let len = arg.length;
        let ptr = malloc(len, 1) >>> 0;

        const mem = getUint8ArrayMemory0();

        let offset = 0;

        for (; offset < len; offset++) {
            const code = arg.charCodeAt(offset);
            if (code > 0x7F) break;
            mem[ptr + offset] = code;
        }
        if (offset !== len) {
            if (offset !== 0) {
                arg = arg.slice(offset);
            }
            ptr = realloc(ptr, len, len = offset + arg.length * 3, 1) >>> 0;
            const view = getUint8ArrayMemory0().subarray(ptr + offset, ptr + len);
            const ret = cachedTextEncoder.encodeInto(arg, view);

            offset += ret.written;
            ptr = realloc(ptr, len, offset, 1) >>> 0;
        }

        WASM_VECTOR_LEN = offset;
        return ptr;
    }

    function takeFromExternrefTable0(idx) {
        const value = wasm.__wbindgen_externrefs.get(idx);
        wasm.__externref_table_dealloc(idx);
        return value;
    }

    let cachedTextDecoder = new TextDecoder('utf-8', { ignoreBOM: true, fatal: true });
    cachedTextDecoder.decode();
    function decodeText(ptr, len) {
        return cachedTextDecoder.decode(getUint8ArrayMemory0().subarray(ptr, ptr + len));
    }

    const cachedTextEncoder = new TextEncoder();

    if (!('encodeInto' in cachedTextEncoder)) {
        cachedTextEncoder.encodeInto = function (arg, view) {
            const buf = cachedTextEncoder.encode(arg);
            view.set(buf);
            return {
                read: arg.length,
                written: buf.length
            };
        };
    }

    let WASM_VECTOR_LEN = 0;

    let wasmModule, wasmInstance, wasm;
    function __wbg_finalize_init(instance, module) {
        wasmInstance = instance;
        wasm = instance.exports;
        wasmModule = module;
        cachedBigUint64ArrayMemory0 = null;
        cachedDataViewMemory0 = null;
        cachedUint8ArrayMemory0 = null;
        wasm.__wbindgen_start();
        return wasm;
    }

    async function __wbg_load(module, imports) {
        if (typeof Response === 'function' && module instanceof Response) {
            if (typeof WebAssembly.instantiateStreaming === 'function') {
                try {
                    return await WebAssembly.instantiateStreaming(module, imports);
                } catch (e) {
                    const validResponse = module.ok && expectedResponseType(module.type);

                    if (validResponse && module.headers.get('Content-Type') !== 'application/wasm') {
                        console.warn("`WebAssembly.instantiateStreaming` failed because your server does not serve Wasm with `application/wasm` MIME type. Falling back to `WebAssembly.instantiate` which is slower. Original error:\n", e);

                    } else { throw e; }
                }
            }

            const bytes = await module.arrayBuffer();
            return await WebAssembly.instantiate(bytes, imports);
        } else {
            const instance = await WebAssembly.instantiate(module, imports);

            if (instance instanceof WebAssembly.Instance) {
                return { instance, module };
            } else {
                return instance;
            }
        }

        function expectedResponseType(type) {
            switch (type) {
                case 'basic': case 'cors': case 'default': return true;
            }
            return false;
        }
    }

    function initSync(module) {
        if (wasm !== undefined) return wasm;


        if (module !== undefined) {
            if (Object.getPrototypeOf(module) === Object.prototype) {
                ({module} = module)
            } else {
                console.warn('using deprecated parameters for `initSync()`; pass a single object instead')
            }
        }

        const imports = __wbg_get_imports();
        if (!(module instanceof WebAssembly.Module)) {
            module = new WebAssembly.Module(module);
        }
        const instance = new WebAssembly.Instance(module, imports);
        return __wbg_finalize_init(instance, module);
    }

    async function __wbg_init(module_or_path) {
        if (wasm !== undefined) return wasm;


        if (module_or_path !== undefined) {
            if (Object.getPrototypeOf(module_or_path) === Object.prototype) {
                ({module_or_path} = module_or_path)
            } else {
                console.warn('using deprecated parameters for the initialization function; pass a single object instead')
            }
        }


        const imports = __wbg_get_imports();

        if (typeof module_or_path === 'string' || (typeof Request === 'function' && module_or_path instanceof Request) || (typeof URL === 'function' && module_or_path instanceof URL)) {
            module_or_path = fetch(module_or_path);
        }

        const { instance, module } = await __wbg_load(await module_or_path, imports);

        return __wbg_finalize_init(instance, module);
    }

    return Object.assign(__wbg_init, { initSync }, exports);
})({ __proto__: null });
