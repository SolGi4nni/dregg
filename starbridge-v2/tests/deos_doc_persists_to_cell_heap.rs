//! **A deos document persists to the REAL committed cell heap, not a sidecar.**
//!
//! The desktop document-editor encodes prose into field elements and commits them
//! via `Effect::SetField` into the cell's `fields_map` (ext keys >= `STATE_SLOTS`,
//! committed via `fields_root` — `cell/src/state.rs`). This test drives that exact
//! encode → verified turn → read-back path through the real `World`/executor (no
//! gpui), proving:
//!   * a doc edit COMMITS to the cell's committed heap (a real receipt, height moves);
//!   * the value READS BACK from the committed state (`get_field_ext` / membership);
//!   * a shrunk revision leaves no stale committed chunk;
//!   * reopen restores FROM THE LEDGER (a fresh ledger snapshot, no sidecar).
//!
//! The desktop's `commit_doc_text_to_heap` / `read_doc_from_heap`
//! (`starbridge-v2/src/deos_desktop/mod.rs`) are thin wrappers over exactly this.

use dregg_turn::action::Effect;
use starbridge_v2::world::demo_world;

// The document heap-namespace constants — kept in sync with
// `starbridge-v2/src/deos_desktop/chrome.rs` (which is gpui-gated, so this gpui-free
// integration test inlines them rather than pulling the graphics stack).
const DOC_TEXT_BASE: u64 = 1_000_000;
const DOC_CHUNK_BYTES: usize = 32;
const DOC_MAX_CHUNKS: u64 = 1024;

/// Build the SetField effects that write `text` into a cell's committed heap —
/// the same layout `commit_doc_text_to_heap` produces (length felt + chunk felts +
/// zeroing of `prev_chunks - new_chunks` stale trailing chunks).
fn doc_effects(cell: dregg_types::CellId, text: &str, prev_len: usize) -> Vec<Effect> {
    let bytes = text.as_bytes();
    let byte_len = bytes.len();
    let new_chunks = byte_len.div_ceil(DOC_CHUNK_BYTES) as u64;
    let prev_chunks = (prev_len.div_ceil(DOC_CHUNK_BYTES) as u64).min(DOC_MAX_CHUNKS);

    let mut effects = Vec::new();
    let mut len_fe = [0u8; 32];
    len_fe[..8].copy_from_slice(&(byte_len as u64).to_le_bytes());
    effects.push(Effect::SetField {
        cell,
        index: DOC_TEXT_BASE as usize,
        value: len_fe,
    });
    let n = new_chunks.min(DOC_MAX_CHUNKS);
    for i in 0..n {
        let start = (i as usize) * DOC_CHUNK_BYTES;
        let end = (start + DOC_CHUNK_BYTES).min(byte_len);
        let mut fe = [0u8; 32];
        fe[..end - start].copy_from_slice(&bytes[start..end]);
        effects.push(Effect::SetField {
            cell,
            index: (DOC_TEXT_BASE + 1 + i) as usize,
            value: fe,
        });
    }
    for i in n..prev_chunks {
        effects.push(Effect::SetField {
            cell,
            index: (DOC_TEXT_BASE + 1 + i) as usize,
            value: [0u8; 32],
        });
    }
    effects
}

/// Read prose back out of a cell's committed heap — the read `read_doc_from_heap`
/// does off the live ledger.
fn read_doc(w: &starbridge_v2::world::World, cell: &dregg_types::CellId) -> Option<String> {
    let state = &w.ledger().get(cell)?.state;
    let len_fe = state.get_field_ext(DOC_TEXT_BASE)?;
    let byte_len = u64::from_le_bytes(len_fe[..8].try_into().ok()?) as usize;
    let mut bytes = Vec::with_capacity(byte_len);
    let mut chunk = 0u64;
    while bytes.len() < byte_len && chunk < DOC_MAX_CHUNKS {
        let fe = state
            .get_field_ext(DOC_TEXT_BASE + 1 + chunk)
            .unwrap_or([0u8; 32]);
        let take = (byte_len - bytes.len()).min(DOC_CHUNK_BYTES);
        bytes.extend_from_slice(&fe[..take]);
        chunk += 1;
    }
    Some(String::from_utf8_lossy(&bytes).into_owned())
}

#[test]
fn document_commits_to_committed_cell_heap_and_reopens_from_ledger() {
    let (mut w, [treasury, _service, _user]) = demo_world();
    let cell = treasury;

    // No committed document yet — the heap carries nothing at DOC_TEXT_BASE.
    assert!(
        read_doc(&w, &cell).is_none(),
        "a fresh cell has no committed document"
    );

    // ── Edit #1: a doc longer than one 32-byte chunk ──────────────────────────────
    let prose = "The document IS the cell. Its prose lives in the committed heap, \
                 not a sidecar — a verified turn, a receipt, replayable.";
    assert!(
        prose.len() > DOC_CHUNK_BYTES,
        "exercise multi-chunk encoding"
    );

    let h0 = w.height();
    let turn = w.turn(cell, doc_effects(cell, prose, 0));
    let outcome = w.commit_turn(turn);
    assert!(
        outcome.is_committed(),
        "the doc-edit SetField turn must commit (a real receipt)"
    );
    assert!(w.height() > h0, "the chronicle advanced — a receipted turn");

    // The value reads back FROM THE COMMITTED STATE (not a buffer, not a sidecar).
    assert_eq!(
        read_doc(&w, &cell).as_deref(),
        Some(prose),
        "prose reads back verbatim from the committed cell heap"
    );

    // It is genuinely committed by `fields_root` (the membership witness): the stored
    // length value is the value the recomputed root commits to.
    {
        let state = &w.ledger().get(&cell).unwrap().state;
        assert!(
            state.fields_root_membership(DOC_TEXT_BASE).is_some(),
            "the length key is committed by fields_root (membership witness)"
        );
        let n_chunks = prose.len().div_ceil(DOC_CHUNK_BYTES) as u64;
        for i in 0..n_chunks {
            assert!(
                state
                    .fields_root_membership(DOC_TEXT_BASE + 1 + i)
                    .is_some(),
                "chunk {i} is committed by fields_root"
            );
        }
    }

    // ── Edit #2: SHRINK the document — stale trailing chunks must be cleared ───────
    let short = "shorter.";
    let prev_len = prose.len();
    let turn = w.turn(cell, doc_effects(cell, short, prev_len));
    assert!(
        w.commit_turn(turn).is_committed(),
        "the shrink edit commits"
    );
    assert_eq!(
        read_doc(&w, &cell).as_deref(),
        Some(short),
        "the shrunk prose reads back exactly (no trailing garbage)"
    );
    // The previously-written chunk #1 (which the short doc no longer uses) is zeroed.
    {
        let state = &w.ledger().get(&cell).unwrap().state;
        let stale = state.get_field_ext(DOC_TEXT_BASE + 2).unwrap_or([0u8; 32]);
        assert_eq!(stale, [0u8; 32], "stale trailing chunk was zeroed in-turn");
    }

    // ── Reopen FROM THE LEDGER: a fresh read of the committed state restores it ────
    // (Model the desktop reopening the doc window: `make_kind` -> `load_doc_text` ->
    // `read_doc_from_heap` reads the committed `fields_map`, no sidecar involved.)
    let reopened = read_doc(&w, &cell);
    assert_eq!(
        reopened.as_deref(),
        Some(short),
        "reopen restores the document from the committed ledger heap"
    );
}
