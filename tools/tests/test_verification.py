"""Regression tests for false-success cases in the release checks."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from axiom_audit import audit
import certificate
import check_axioms
import check_manifest
import hashlib
from check_exponents import paper_exponents


class AxiomAuditTests(unittest.TestCase):
    def result(self, text, code=0):
        return subprocess.CompletedProcess([], code, text, "")

    def test_all_standard_and_no_axioms(self):
        output = "'one' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        output += "'two' does not depend on any axioms\n"
        self.assertEqual(set(audit(self.result(output), ["one", "two"])), {"one", "two"})

    def test_nonzero_lean_exit_even_with_axiom_output(self):
        with self.assertRaisesRegex(ValueError, "Lean exited"):
            audit(self.result("'one' depends on axioms: [propext]", 1), ["one"])

    def test_missing_export(self):
        with self.assertRaisesRegex(ValueError, "missing axiom output"):
            audit(self.result("'one' depends on axioms: [propext]"), ["one", "two"])

    def test_sorry_and_custom_axioms(self):
        for axiom in ["sorryAx", "UnprovedClaim"]:
            with self.subTest(axiom=axiom), self.assertRaisesRegex(ValueError, "unexpected axioms"):
                audit(self.result(f"'one' depends on axioms: [{axiom}]"), ["one"])

    def test_duplicate_output(self):
        with self.assertRaisesRegex(ValueError, "duplicate"):
            audit(self.result("'one' depends on axioms: [propext]\n" * 2), ["one"])

    def test_emit_does_not_modify_manifest_on_missing_output(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "ledger").mkdir()
            manifest = root / "ledger/manifest.yaml"
            original = "nodes:\n  - id: one\n    file: ORRW/One.lean\n    export: one\n    state: SEALED\n"
            manifest.write_text(original)
            with patch.object(check_axioms, "ROOT", root), patch.object(sys, "argv", ["check_axioms", "--emit"]), patch.object(check_axioms.subprocess, "run", return_value=self.result("")):
                with self.assertRaises(ValueError):
                    check_axioms.main()
            self.assertEqual(manifest.read_text(), original)

    def test_failed_certificate_preserves_existing_file(self):
        with tempfile.TemporaryDirectory() as td:
            out = Path(td) / "CERTIFICATE.md"
            out.write_text("previous checked certificate\n")
            with patch.object(certificate, "OUT", out), patch.object(certificate, "build", side_effect=ValueError("Lean failed")):
                self.assertEqual(certificate.main(), 1)
            self.assertEqual(out.read_text(), "previous checked certificate\n")

    def test_certificate_rejects_incomplete_probe(self):
        with tempfile.TemporaryDirectory() as td:
            with patch.object(certificate, "ROOT", Path(td)), patch.object(certificate, "module_names", return_value=[]), patch.object(certificate, "run", return_value=self.result("")):
                with self.assertRaisesRegex(ValueError, "missing axiom output"):
                    certificate.axiom_lines(["one"])

    def test_failed_build_never_certifies(self):
        # Empty manifest isolates the build failure from source checks.
        with tempfile.TemporaryDirectory() as td:
            manifest = Path(td) / "manifest.yaml"
            manifest.write_text("nodes: []\n")
            def run(cmd, **kwargs):
                return self.result("", 1 if cmd[0] == "lake" else 0)
            with patch.object(certificate, "MANIFEST", manifest), patch.object(certificate, "run", side_effect=run):
                with self.assertRaisesRegex(ValueError, "Lean build failed"):
                    certificate.build()

    def test_manuscript_hash_detects_changed_source(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "paper.tex").write_text("original")
            pin = {"source_pin": {"file": "paper.tex", "sha256": hashlib.sha256(b"original").hexdigest()}}
            with patch.object(check_manifest, "ROOT", root):
                check_manifest.check_source_pin(pin)
                (root / "paper.tex").write_text("changed")
                with self.assertRaisesRegex(ValueError, "source hash mismatch"):
                    check_manifest.check_source_pin(pin)

    def test_fraction_notation_preserves_exponents(self):
        self.assertEqual(paper_exponents(r"n^{\frac{d}{d+1}}"), {"d/(d+1)"})
        self.assertEqual(paper_exponents(r"n^{\frac{d-1}{d+1}}"), {"(d-1)/(d+1)"})
        self.assertNotEqual(paper_exponents(r"n^{\frac{d}{d+2}}"), {"d/(d+1)"})


if __name__ == "__main__":
    unittest.main()
