# VK-REGEN LOG — append-only audit trail of descriptor regen events

Every authorized descriptor install / provenance stamp appends one row
(written by `scripts/emit_descriptors.py`; see docs/VK-REGEN-CONTROLS.md).
Rows are never edited or removed; git history is the tamper-evidence.

| when (UTC) | operator | mode | HEAD:metatheory/Dregg2 | repo HEAD | source dirty | changed |
|---|---|---|---|---|---|---|
| 2026-07-08T01:11:04Z | ember@nextop.local | stamp-existing | 0ec5a7d198833da3095707cdd2ca7408280428de | e2695c236a20b2b8e30615c516965f2f4ffe74b9 | YES | (stamp only) |
| 2026-07-08T01:11:21Z | ember@nextop.local | stamp-existing | 0ec5a7d198833da3095707cdd2ca7408280428de | e2695c236a20b2b8e30615c516965f2f4ffe74b9 | YES | (stamp only) |
