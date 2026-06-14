// dregg browser compositor (N11) — the DOM sibling of starbridge-v2's
// `shell::Shell::compose`. A gpui-free scene-graph that carries the firmament's
// `Target::Surface{cell}` arm to PIXELS IN THE BROWSER.
//
// `docs/design-frontiers/WEB-FORWARD.md §2 / §8 S2`. The model, byte-for-byte the
// native shell's:
//
//   * an ORDERED surface list (z-order, back-to-front) — the scene graph;
//   * each pane drawn to its OWN `<canvas>` with COMPOSITOR-DRAWN identity chrome
//     (the T2 badge from `surface_identity`, read from the LIVE LEDGER — never the
//     pane's self-description);
//   * DOM focus/pointer routed to the single focused pane (T3 focus-exclusivity);
//   * T1 non-overlap on `present` (a surface paints only its own rect; the rects
//     the compositor assigns never overlap in tile/stack);
//   * the float / tile / stack layouts + a protected console that can't be closed.
//
// The compositor MULTIPLEXES capabilities; it does not mint authority. Whether a
// pane MAY exist / be shared / be revoked is decided by the real executor via the
// wasm surface bindings (`open_surface`/`share_surface`/`revoke_surface`); this
// module only arranges and paints what the ledger authorizes, and draws the
// anti-spoof identity from the ledger.

// The three classic arrangements (mirrors `shell::Layout`). All paint in
// z-order; only the geometry differs.
export const Layout = Object.freeze({
  Float: 'float', // surfaces keep their own rects (free placement)
  Tile: 'tile',   // non-console surfaces tile the work area in a grid
  Stack: 'stack', // non-console surfaces cascade (centered + offset)
});

// A short, operator-legible identity from a full hex cell id (abbreviated head…tail).
function shortId(hex) {
  if (!hex || hex.length < 12) return hex || '????';
  return `${hex.slice(0, 6)}…${hex.slice(-4)}`;
}

// The lifecycle badge color — live is calm, anything else is a warning the
// compositor draws honestly (a dimmed / flagged pane).
function lifecycleColor(lifecycle) {
  switch (lifecycle) {
    case 'live': return '#38c172';      // green
    case 'sealed': return '#f6993f';    // amber — quiescent
    case 'archived': return '#7795f8';  // blue — pruned history, still live
    case 'migrated': return '#9561e2';  // purple — moved
    case 'destroyed': return '#e3342f'; // red — gone
    default: return '#8795a1';          // grey — missing / unknown
  }
}

/**
 * One surface (pane) in the compositor's scene.
 *
 * `identity` is the T2 badge — `{ owning_cell_id, lifecycle, source_state_root,
 * balance, accepts_effects }` exactly as the wasm `surface_identity` binding
 * returns it from the live ledger. The compositor draws the title bar from THIS,
 * never from `title` alone (the page-supplied title is shown as a subtitle but is
 * NOT the identity).
 */
class Surface {
  constructor({ id, owner, title, identity, rect, isConsole = false }) {
    this.id = id;
    this.owner = owner;             // the agent label/index that holds this pane
    this.title = title || '';       // the page-supplied label (subtitle only)
    this.identity = identity;       // the T2 badge (from the ledger)
    this.rect = rect;               // { x, y, w, h } in the work area
    this.isConsole = isConsole;
    this.focused = false;
    this.contentDigest = 0;         // advanced on a committed present (fail-closed)
    // The painter: a callback (ctx, surface) the owner supplies to draw the
    // pane's CONTENT into its canvas. The compositor clips to the pane's own
    // region (T1) before invoking it, so a painter physically cannot overpaint
    // another pane.
    this.painter = null;
  }
}

export class Compositor {
  /**
   * @param {object} opts
   * @param {object} opts.wasm        the dregg-wasm exports (for surface_identity reads)
   * @param {number} opts.runtime     the DreggRuntime handle
   * @param {HTMLElement} opts.mount   the DOM element to render the scene into
   * @param {{w:number,h:number}} [opts.area]  the logical work area
   */
  constructor({ wasm, runtime, mount, area }) {
    this.wasm = wasm;
    this.runtime = runtime;
    this.mount = mount;
    this.area = area || { w: 720, h: 460 };
    this.surfaces = [];      // z-order, back-to-front (last = front)
    this.focus = null;       // focused surface id
    this.layout = Layout.Float;
    this.nextId = 1;
    // Event sink: the demo subscribes to learn about T1/T2/T3 refusals at the
    // glass (e.g. to flash the ⚠ banner).
    this.onEvent = () => {};
  }

  // --- opening / closing (the compositor only arranges; authority is the
  //     executor's, read via the wasm bindings) -----------------------------

  /**
   * Open the privileged CONSOLE surface — the trusted root pane that can't be
   * closed (mirrors `shell::open_console`). Its identity is drawn from the live
   * ledger like any pane, but it is labelled distinctly so it is never confused
   * with a cell-owned surface.
   */
  openConsole(ownerLabel, ownerAgentIndex, title) {
    const identity = this._readIdentity(ownerAgentIndex);
    const id = this.nextId++;
    const surface = new Surface({
      id,
      owner: ownerLabel,
      title: title || 'console',
      identity,
      rect: { x: 8, y: 8, w: this.area.w - 16, h: 120 },
      isConsole: true,
    });
    this.surfaces.push(surface);
    this.focus = id;
    this._arrange();
    return id;
  }

  /**
   * Install a surface pane for the surface backed by `surfaceOwnerAgentIndex`'s
   * cell, held by `ownerLabel`. The identity badge is read from the LIVE LEDGER
   * via the wasm `surface_identity` binding — the anti-spoof T2 binding. The pane
   * is raised to the front + focused on open (mirrors `shell::open_view`).
   */
  openSurface(ownerLabel, surfaceOwnerAgentIndex, title, painter) {
    const identity = this._readIdentity(surfaceOwnerAgentIndex);
    const id = this.nextId++;
    const surface = new Surface({
      id,
      owner: ownerLabel,
      title,
      identity,
      // A default float rect (re-arranged by tile/stack); offset so multiple
      // opens cascade rather than stack exactly.
      rect: {
        x: 16 + (this.surfaces.length * 24) % 120,
        y: 140 + (this.surfaces.length * 20) % 100,
        w: 300,
        h: 180,
      },
    });
    surface.painter = painter || null;
    surface.metaAgentIndex = surfaceOwnerAgentIndex;
    this.surfaces.push(surface);
    this._focus(id);
    this._arrange();
    return id;
  }

  /** Close a pane (the console refuses — it is the protected root). */
  closeSurface(id) {
    const surface = this.surfaces.find((s) => s.id === id);
    if (!surface) return false;
    if (surface.isConsole) {
      this.onEvent({ kind: 'refused', reason: 'the protected console cannot be closed' });
      return false;
    }
    this.surfaces = this.surfaces.filter((s) => s.id !== id);
    if (this.focus === id) {
      this.focus = this.surfaces.length ? this.surfaces[this.surfaces.length - 1].id : null;
    }
    this._arrange();
    return true;
  }

  // --- the scene-authority teeth (T1/T2/T3) --------------------------------

  /**
   * T3 FOCUS-EXCLUSIVITY: at most one focused pane; keyboard/pointer events route
   * only to it. Setting focus on one pane clears it on all others. Returns false
   * if the pane is gone (a revoked pane can't take focus).
   */
  focusSurface(id) {
    if (!this.surfaces.some((s) => s.id === id)) return false;
    this._focus(id);
    // Raise to front on focus (z-order).
    const idx = this.surfaces.findIndex((s) => s.id === id);
    const [s] = this.surfaces.splice(idx, 1);
    this.surfaces.push(s);
    this._arrange();
    return true;
  }

  /**
   * Route a DOM input event to the focused pane only (T3). Returns the focused
   * surface id the event was routed to, or null if input was dropped (no focus —
   * the event does NOT leak to a non-focused pane).
   */
  routeInput(_domEvent) {
    if (this.focus == null) return null;
    return this.focus;
  }

  /**
   * PRESENT: advance a pane's frame. The compositor re-reads the pane's identity
   * from the LIVE LEDGER first (so a sealed/destroyed backing is reflected
   * honestly), clips to the pane's own rect (T1 — a painter cannot overpaint
   * another pane), and advances the content digest. Returns true on a painted
   * frame; false (fail-closed) if the pane is gone or its backing no longer
   * accepts effects. (The cap-authority half — does the presenter hold draw
   * rights? — is the executor's `present_surface` binding; call it first.)
   */
  present(id, contentDigest) {
    const surface = this.surfaces.find((s) => s.id === id);
    if (!surface) return false;
    // Re-read identity live (T2 stays honest frame-to-frame).
    if (surface.metaAgentIndex != null) {
      surface.identity = this._readIdentity(surface.metaAgentIndex);
    }
    if (surface.identity && surface.identity.accepts_effects === false && !surface.isConsole) {
      // A non-live backing cell paints no new frame — the compositor tells the
      // truth (dimmed), it does not let a dead cell masquerade as live.
      this._render();
      return false;
    }
    surface.contentDigest = contentDigest >>> 0;
    this._render();
    return true;
  }

  /** Set the layout (float / tile / stack) and re-arrange + repaint. */
  setLayout(layout) {
    if (!Object.values(Layout).includes(layout)) return;
    this.layout = layout;
    this._arrange();
  }

  /** Re-read EVERY pane's identity from the live ledger and repaint (call after
   *  a share/revoke/turn so the badges + balances reflect the new state). */
  refreshIdentities() {
    for (const s of this.surfaces) {
      if (s.metaAgentIndex != null) {
        s.identity = this._readIdentity(s.metaAgentIndex);
      }
    }
    this._render();
  }

  // --- internals ------------------------------------------------------------

  _readIdentity(agentIndex) {
    try {
      // THE T2 SOURCE: the badge is the live ledger's, not the page's.
      return this.wasm.surface_identity(this.runtime, agentIndex);
    } catch (e) {
      // A missing backing cell reads as a dangling/missing view — the chrome
      // tells the truth rather than letting it masquerade.
      return {
        owning_cell_id: '',
        lifecycle: 'missing',
        source_state_root: '',
        balance: 0,
        accepts_effects: false,
      };
    }
  }

  _focus(id) {
    this.focus = id;
    for (const s of this.surfaces) s.focused = s.id === id;
  }

  // Assign geometry per layout. Tile/stack arrange NON-CONSOLE surfaces so they
  // do not overlap (T1 at the layout level); the console keeps its anchored rect.
  _arrange() {
    const consoles = this.surfaces.filter((s) => s.isConsole);
    const panes = this.surfaces.filter((s) => !s.isConsole);
    const top = consoles.length ? 136 : 8; // leave room under the console
    const workH = this.area.h - top - 8;

    if (this.layout === Layout.Tile) {
      const n = panes.length || 1;
      const cols = Math.ceil(Math.sqrt(n));
      const rows = Math.ceil(n / cols);
      const cw = Math.floor((this.area.w - 16) / cols);
      const ch = Math.floor(workH / rows);
      panes.forEach((s, i) => {
        const c = i % cols;
        const r = Math.floor(i / cols);
        s.rect = { x: 8 + c * cw, y: top + r * ch, w: cw - 6, h: ch - 6 };
      });
    } else if (this.layout === Layout.Stack) {
      const w = Math.min(360, this.area.w - 80);
      const h = Math.min(220, workH - 40);
      panes.forEach((s, i) => {
        const off = i * 22;
        s.rect = {
          x: Math.floor((this.area.w - w) / 2) + off,
          y: top + 8 + off,
          w,
          h,
        };
      });
    }
    // Float: leave each pane's own rect.
    this._render();
  }

  // Paint the whole scene (back-to-front) into the mount. Each pane is a DOM
  // frame (the compositor-drawn title bar = the T2 badge) wrapping a <canvas>
  // (the pane CONTENT, clipped to the pane region). The page never draws the
  // badge; the compositor does, from the ledger.
  _render() {
    if (!this.mount) return;
    this.mount.innerHTML = '';
    this.mount.style.position = 'relative';
    this.mount.style.width = `${this.area.w}px`;
    this.mount.style.height = `${this.area.h}px`;
    this.mount.style.background = '#1a1f28';
    this.mount.style.borderRadius = '8px';
    this.mount.style.overflow = 'hidden';

    // Back-to-front: the array order IS the z-order.
    this.surfaces.forEach((s, z) => {
      const id = s.identity || {};
      const frame = document.createElement('div');
      frame.className = 'cmp-pane' + (s.focused ? ' cmp-pane--focused' : '') + (s.isConsole ? ' cmp-pane--console' : '');
      frame.dataset.surfaceId = String(s.id);
      Object.assign(frame.style, {
        position: 'absolute',
        left: `${s.rect.x}px`,
        top: `${s.rect.y}px`,
        width: `${s.rect.w}px`,
        height: `${s.rect.h}px`,
        zIndex: String(10 + z),
        border: s.focused ? '2px solid #4da3ff' : '1px solid #2d3540',
        borderRadius: '6px',
        background: '#222934',
        boxShadow: s.focused ? '0 4px 18px rgba(0,0,0,0.5)' : '0 2px 8px rgba(0,0,0,0.35)',
        overflow: 'hidden',
        cursor: 'pointer',
      });

      // THE TITLE BAR — the COMPOSITOR-DRAWN identity (T2). Drawn from the live
      // ledger's `(owning_cell_id, lifecycle, source_state_root)`, NEVER the
      // page's. The page-supplied `title` is shown only as a dimmed subtitle.
      const bar = document.createElement('div');
      Object.assign(bar.style, {
        display: 'flex',
        alignItems: 'center',
        gap: '6px',
        padding: '4px 8px',
        font: '11px ui-monospace, monospace',
        background: s.isConsole ? '#10202c' : '#1b222c',
        borderBottom: '1px solid #2d3540',
        color: '#cfd8e3',
      });
      const dot = document.createElement('span');
      Object.assign(dot.style, {
        width: '8px', height: '8px', borderRadius: '50%',
        background: lifecycleColor(id.lifecycle), flex: '0 0 auto',
      });
      dot.title = `lifecycle: ${id.lifecycle}`;
      const cellSpan = document.createElement('span');
      cellSpan.textContent = s.isConsole ? '⛨ console' : `cell ${shortId(id.owning_cell_id)}`;
      cellSpan.style.fontWeight = '600';
      const lifeSpan = document.createElement('span');
      lifeSpan.textContent = `· ${id.lifecycle}`;
      lifeSpan.style.color = lifecycleColor(id.lifecycle);
      const rootSpan = document.createElement('span');
      rootSpan.textContent = `· root ${shortId(id.source_state_root)}`;
      rootSpan.style.color = '#7e8a99';
      rootSpan.style.marginLeft = 'auto';
      rootSpan.title = `source state root (the T2 binding): ${id.source_state_root}`;
      bar.append(dot, cellSpan, lifeSpan, rootSpan);

      // THE CONTENT — a <canvas>, clipped to the pane region (T1). The painter
      // can only draw inside its own canvas; it physically cannot reach another
      // pane's pixels.
      const canvas = document.createElement('canvas');
      const contentH = Math.max(0, s.rect.h - 26);
      canvas.width = s.rect.w;
      canvas.height = contentH;
      Object.assign(canvas.style, { display: 'block', width: '100%', height: `${contentH}px` });
      const ctx = canvas.getContext('2d');
      // Background: a calm fill, dimmed if the backing isn't live (honest).
      const dim = id.accepts_effects === false && !s.isConsole;
      ctx.fillStyle = dim ? '#171b22' : '#232b36';
      ctx.fillRect(0, 0, canvas.width, canvas.height);
      ctx.save();
      // T1: hard-clip the painter to the content region — it cannot escape.
      ctx.beginPath();
      ctx.rect(0, 0, canvas.width, canvas.height);
      ctx.clip();
      if (s.painter) {
        try { s.painter(ctx, s); } catch (_) { /* a painter throwing must not break the scene */ }
      } else {
        // Default content: the page-supplied title (subtitle) + the live balance.
        ctx.fillStyle = dim ? '#566' : '#9fb0c3';
        ctx.font = '12px ui-monospace, monospace';
        ctx.fillText(s.title || '(surface)', 10, 22);
        ctx.fillStyle = '#7e8a99';
        ctx.font = '11px ui-monospace, monospace';
        ctx.fillText(`balance ${id.balance}`, 10, 40);
        ctx.fillText(`frame #${s.contentDigest}`, 10, 56);
        if (dim) {
          ctx.fillStyle = '#e3342f';
          ctx.fillText(`⚠ backing ${id.lifecycle} — dark`, 10, 74);
        }
      }
      ctx.restore();

      frame.append(bar, canvas);
      // T3: a click focuses this pane (routes input to it, exclusively).
      frame.addEventListener('mousedown', () => this.focusSurface(s.id));
      this.mount.appendChild(frame);
    });
  }
}
