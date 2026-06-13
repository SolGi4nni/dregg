"""`dregg.deploy` — DreggDL, the checkable deployment spec, through the binding.

These exercise the REAL `dregg-deploy` pipeline (parse → `Lowered::from_deployment`
→ `dregg_userspace_verify::analyze`) via the pyo3 `dregg.deploy.{check,lower}`
functions — the exact same code the `dregg-deploy check` CLI runs. Nothing here
reimplements the lowering or the userspace-verify.
"""

import dregg
import dregg.deploy as deploy
import pytest


# A valid escrow deployment (the reference layout): an escrow factory, three
# cells born from it, one funding transfer, one in-band operator adopt grant.
VALID_ESCROW = """
[federation]
id = "auto"

[[factory]]
ref = "escrow"
default_mode = "hosted"
creation_budget = 100

  [[factory.state_constraint]]
  kind = "write_once"
  slot = 3

  [[factory.allowed_cap_template]]
  permissions = "signature"
  target = "self"
  attenuatable = true

[[cell]]
name = "deal-001"
factory = "escrow"
mode = "hosted"
initial_fields = [ { slot = 3, value = 42 } ]

[[cell]]
name = "operator"
factory = "escrow"

[[cell]]
name = "bank"
factory = "escrow"

[[fund]]
from = "bank"
to = "deal-001"
amount = 1000

[[grant]]
from = "deal-001"
to = "operator"
permissions = "signature"
target = "deal-001"
"""


# An OVER-GRANTING deployment: `deal` hands `operator` a TRANSFER-ONLY facet
# (allowed_effects = 2) over `deal`; `operator` then re-delegates to `sub` an
# UNRESTRICTED cap over the SAME target (allowed_effects absent = top). That
# widens what it was handed → an in-forest amplification along the delegation
# edge, which non-amplification (guarantee A) catches.
OVER_GRANTING = """
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "deal"
factory = "f"
[[cell]]
name = "operator"
factory = "f"
[[cell]]
name = "sub"
factory = "f"

[[grant]]
from = "deal"
to = "operator"
permissions = "signature"
target = "deal"
allowed_effects = 2

[[grant]]
from = "operator"
to = "sub"
permissions = "signature"
target = "deal"
"""


def test_valid_escrow_passes():
    v = deploy.check(VALID_ESCROW)
    assert v["pass"] is True, f"valid escrow must PASS; findings: {v['assurance']['findings']}"
    # 3 births + 1 fund + 1 grant = 5 root effect-groups.
    assert v["turn_count"] == 5
    assert len(v["cells"]) == 3
    assert len(v["factories"]) == 1
    # The assurance carries the four located checks, all passing.
    a = v["assurance"]
    assert a["pass"] is True
    for check in ("conservation", "no_amplification", "wellformed", "ring_balance"):
        assert a[check]["pass"] is True, f"{check} should pass on a valid deployment"


def test_resolved_ids_are_deterministic():
    a = deploy.check(VALID_ESCROW)
    b = deploy.check(VALID_ESCROW)
    assert a["cells"] == b["cells"], "cell ids are a deterministic function of names"
    assert a["factories"] == b["factories"], "factory_vks are deterministic"


def test_over_granting_fails_with_locus():
    v = deploy.check(OVER_GRANTING)
    assert v["pass"] is False, "an over-granting deployment must FAIL"
    a = v["assurance"]
    assert a["no_amplification"]["pass"] is False, "non-amplification (A) must catch the widening"
    findings = a["no_amplification"]["findings"]
    assert findings, "the failing check carries findings"
    # The finding names the amplification AND locates the offending grant effect.
    assert any("amplif" in f["message"].lower() for f in findings), (
        f"a finding names the amplification; got: {[f['message'] for f in findings]}"
    )
    assert findings[0]["locus"]["effect_index"] is not None, (
        "the finding locates the offending grant effect"
    )


def test_unknown_factory_errors_with_name():
    bad = """
[federation]
id = "auto"
[[cell]]
name = "c"
factory = "does-not-exist"
"""
    with pytest.raises(dregg.DreggError) as ei:
        deploy.check(bad)
    assert "does-not-exist" in str(ei.value), "the error names the missing factory"


def test_unbalanced_ring_is_caught():
    # a→b, b→c but no c→a: with ring=True the participants don't all net to zero.
    open_ring = """
[federation]
id = "auto"
[[factory]]
ref = "f"
[[cell]]
name = "a"
factory = "f"
[[cell]]
name = "b"
factory = "f"
[[cell]]
name = "c"
factory = "f"
[[fund]]
from = "a"
to = "b"
amount = 10
[[fund]]
from = "b"
to = "c"
amount = 10
"""
    v = deploy.check(open_ring, ring=True)
    assert v["assurance"]["ring_balance"]["pass"] is False, "an un-closed ring fails the ring check"
    closed = open_ring + '\n[[fund]]\nfrom = "c"\nto = "a"\namount = 10\n'
    vc = deploy.check(closed, ring=True)
    assert vc["assurance"]["ring_balance"]["pass"] is True, "a closed conserving ring passes"


def test_lower_emits_the_forest():
    lowered = deploy.lower(VALID_ESCROW)
    # The lowering is the REAL Lowered::from_deployment → CallForest.
    forest = lowered["forest"]
    assert "roots" in forest, "the lowered artifact is a CallForest"
    assert len(forest["roots"]) == 5, "3 births + 1 fund + 1 grant"
    assert len(lowered["cells"]) == 3
    assert len(lowered["factories"]) == 1
    # Federation `auto` lowers to the all-zeros placeholder.
    assert lowered["federation_id"] == "00" * 32


def test_lower_is_deterministic():
    a = deploy.lower(VALID_ESCROW)
    b = deploy.lower(VALID_ESCROW)
    assert a["forest"] == b["forest"], "lowering the same DreggDL yields the same forest"


def test_json_surface_parses():
    # A leading `{` selects the JSON surface; it must agree with the TOML one.
    import json
    # Minimal JSON deployment equivalent to a one-factory/one-cell layout.
    dep = {
        "federation": {"id": "auto", "node": ""},
        "factory": [{"ref": "f", "default_mode": "hosted"}],
        "cell": [{"name": "c", "factory": "f"}],
    }
    v = deploy.check(json.dumps(dep))
    assert v["pass"] is True
    assert v["turn_count"] == 1
