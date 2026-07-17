#!/usr/bin/env python3
"""Tests for emit_token.py — above all, the DERIVATION honesty teeth.

The safe emit's claim is: "derived from the FV'd template
chain/contracts/launchpad/DreggLaunchToken.sol by count-checked substitutions;
every function body carried byte-for-byte." These tests make that claim
falsifiable:

  * every pedigree function body in the emitted contract is byte-identical to
    the template's (the positive);
  * a template whose declared anchors drifted makes the emit FAIL LOUDLY
    (the drift tooth);
  * an emitted contract whose mint diverged from the template is REFUSED by
    verify_derivation (the divergence tooth);
  * the spec's parameters really land (cap literal, name/symbol/decimals);
  * the unsafe variant stays the honest, hand-written catch-me contract.

Run: python3 tools/token-factory/test_emit_token.py
"""
import unittest

import emit_token

GOOD_SPEC = {
    "name": "Good Capped Token",
    "symbol": "GOOD",
    "decimals": 18,
    "cap": 1_000_000_000,
    "mint_authority": "launchpad-oneshot",
    "tokenomics": {"creator_allocation_bps": 500, "vesting": "12-month linear"},
}

RUG_SPEC = {
    "name": "Refillable Moon Token",
    "symbol": "RMOON",
    "decimals": 18,
    "cap": 1_000_000,
    "mint_authority": "owner-refillable",
}


class TestSafeEmitDerivation(unittest.TestCase):
    def setUp(self):
        self.template = emit_token.read_template()
        self.emitted = emit_token.emit_safe(GOOD_SPEC)

    def test_every_pedigree_function_is_byte_identical(self):
        for fname in emit_token.PEDIGREE_FUNCTIONS:
            body = emit_token.extract_function(self.template, fname)
            self.assertIn(
                body, self.emitted,
                f"{fname} body in the emitted contract differs from the FV'd template",
            )

    def test_parameters_land(self):
        self.assertIn("contract GoodCappedTokenLaunch {", self.emitted)
        self.assertIn('string public constant name = "Good Capped Token";', self.emitted)
        self.assertIn('string public constant symbol = "GOOD";', self.emitted)
        self.assertIn("uint8 public constant decimals = 18;", self.emitted)
        # 1e9 whole tokens at 18 decimals = 1e27 base units, as a source literal.
        self.assertIn(f"uint256 public constant cap = {10**27};", self.emitted)

    def test_template_storage_shapes_are_substituted_not_kept(self):
        self.assertNotIn("immutable cap", self.emitted)
        self.assertNotIn("ZeroCap", self.emitted)
        self.assertNotIn("string memory name_", self.emitted)
        self.assertIn("constructor(address minter_)", self.emitted)

    def test_template_doc_comment_is_preserved(self):
        # The FV'd template's own @title doc block rides along verbatim.
        self.assertIn("/// @title DreggLaunchToken", self.emitted)
        self.assertIn("EMITTED by tools/token-factory", self.emitted)
        self.assertIn("DERIVED from the FV'd template", self.emitted)

    def test_no_rug_doors_in_emitted_source(self):
        for door in ["onlyOwner", "selfdestruct", "delegatecall", "blacklist",
                     "whenNotPaused", "setFee"]:
            self.assertNotIn(door, self.emitted)

    def test_drift_tooth_anchor_changed(self):
        # A template whose constructor no longer matches the declared anchor
        # must refuse the emit, not silently diverge.
        drifted = self.template.replace("if (cap_ == 0) revert ZeroCap();",
                                        "if (cap_ == 0) revert ZeroCap(); // audited")
        orig = emit_token.read_template
        emit_token.read_template = lambda: drifted
        try:
            with self.assertRaises(SystemExit) as cm:
                emit_token.emit_safe(GOOD_SPEC)
            self.assertIn("TEMPLATE DRIFT", str(cm.exception))
        finally:
            emit_token.read_template = orig

    def test_divergence_tooth_verify_derivation(self):
        # An emitted contract whose mint body differs from the template's is refused.
        tampered = self.emitted.replace(
            "if (minted) revert AlreadyMinted();", "", 1
        )
        with self.assertRaises(SystemExit) as cm:
            emit_token.verify_derivation(self.template, tampered)
        self.assertIn("DERIVATION VIOLATION", str(cm.exception))


class TestUnsafeEmit(unittest.TestCase):
    def test_unsafe_variant_shape(self):
        out = emit_token.emit_unsafe(RUG_SPEC, "owner-refillable")
        self.assertIn("contract RefillableMoonTokenLaunch {", out)
        self.assertIn("onlyOwner", out)
        # The rug: no one-shot latch, no cap guard in mint.
        self.assertNotIn("AlreadyMinted", out)
        self.assertNotIn("CapExceeded", out)
        self.assertIn("UNSAFE variant", out)


class TestSpecValidation(unittest.TestCase):
    def test_sol_str_rejects_escapes(self):
        with self.assertRaises(SystemExit):
            emit_token.sol_str('evil " quote')

    def test_identifier_sanitizes(self):
        self.assertEqual(emit_token.solidity_identifier("Good Capped Token"),
                         "GoodCappedToken")
        self.assertEqual(emit_token.solidity_identifier("42dog!"), "Tok42dog")


if __name__ == "__main__":
    unittest.main()
