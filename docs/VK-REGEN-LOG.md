# VK-REGEN LOG — append-only audit trail of descriptor regen events

Every authorized descriptor install / provenance stamp appends one row
(written by `scripts/emit_descriptors.py`; see docs/VK-REGEN-CONTROLS.md).
Rows are never edited or removed; git history is the tamper-evidence.

| when (UTC) | operator | mode | HEAD:metatheory/Dregg2 | repo HEAD | source dirty | changed |
|---|---|---|---|---|---|---|
| 2026-07-08T01:11:04Z | ember@nextop.local | stamp-existing | 0ec5a7d198833da3095707cdd2ca7408280428de | e2695c236a20b2b8e30615c516965f2f4ffe74b9 | YES | (stamp only) |
| 2026-07-08T01:11:21Z | ember@nextop.local | stamp-existing | 0ec5a7d198833da3095707cdd2ca7408280428de | e2695c236a20b2b8e30615c516965f2f4ffe74b9 | YES | (stamp only) |
| 2026-07-12T01:27:23Z | ember@nextop.local | emit | 55e8e44db5a1754b1edc3e4d11f575b69934fadc | 73c3cb380916dfbd2d1f9591ca7b19e178bfe25e | YES | dregg-cross-cell-conservation-v2.json, rotation-v3-staged-registry.tsv, rotation-wide-registry-staged.tsv, rotation-wide-transfer-staged.tsv, rotation-wide-umem-welded-registry-staged.tsv, circuit/src/effect_vm_descriptors.rs |
| 2026-07-12T05:28:47Z | ember@nextop.local | emit | 09d05bf6e8130961304192c09a432900d1100d8a | 18846d7e1846111196fa225937dd7cc616dd01c3 | YES | rotation-wide-registry-staged.tsv, rotation-wide-transfer-staged.tsv, rotation-wide-umem-welded-registry-staged.tsv, circuit/src/effect_vm_descriptors.rs |
| 2026-07-12T05:45:44Z | ember@nextop.local | stamp-existing | b70336374b0b4356378769985d6b7ded19b3e797 | 62de9e359db49df163b5770d5c9536c02de29a33 | YES | (stamp only) |
| 2026-07-12T05:55:10Z | ember@nextop.local | emit | f83dedecd00094790acc2c305fa5e6a93d21d531 | 8e65c07829a27eca0606d8f6794ba0347cb50368 | YES | rotation-v3-staged-registry.tsv, rotation-wide-registry-staged.tsv, rotation-wide-umem-welded-registry-staged.tsv, circuit/src/effect_vm_descriptors.rs |
