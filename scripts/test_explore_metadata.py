"""Regression checks for the explorer's extraction metadata."""
import copy
import hashlib
from pathlib import Path
import tempfile
import unittest

from explore_metadata import enrich


class MetadataTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / "docs").mkdir()
        (self.root / "NLAlib").mkdir()
        (self.root / "NLAlib/Example.lean").write_bytes(b"-- a source file\n")
        self.registry = self.root / "docs/constants.toml"
        self.registry.write_text('[[constant]]\nname = "NLAlib.bound"\n')
        self.data = {"modules": [{"path": "NLAlib/Example.lean"}],
                     "decls": [{"name": "NLAlib.bound"}, {"name": "NLAlib.concept"}]}

    def test_support_role_preserves_declarations_and_hashes_source(self):
        original = copy.deepcopy(self.data)
        result = enrich(self.data, self.root)
        self.assertEqual(result["decls"][0]["explorerRole"], "support")
        self.assertNotIn("explorerRole", result["decls"][1])
        self.assertEqual([d["name"] for d in result["decls"]],
                         [d["name"] for d in original["decls"]])
        self.assertEqual(result["sourceHashes"]["NLAlib/Example.lean"],
                         hashlib.sha256(b"-- a source file\n").hexdigest())

    def test_explicit_concept_override(self):
        with self.registry.open("a") as out:
            out.write('explorer_role = "concept"\n')
        self.assertEqual(enrich(self.data, self.root)["decls"][0]["explorerRole"], "concept")

    def test_invalid_role_and_missing_bound_fail(self):
        with self.registry.open("a") as out:
            out.write('explorer_role = "hidden"\n')
        with self.assertRaisesRegex(ValueError, "invalid explorer_role"):
            enrich(self.data, self.root)
        self.registry.write_text('[[constant]]\nname = "NLAlib.missing"\n')
        with self.assertRaisesRegex(ValueError, "missing from extraction"):
            enrich(self.data, self.root)

    def test_unsafe_path_fails(self):
        for path in ("../outside.lean", "/tmp/outside.lean"):
            with self.subTest(path=path):
                self.data["modules"][0]["path"] = path
                with self.assertRaisesRegex(ValueError, "unsafe module path"):
                    enrich(self.data, self.root)


if __name__ == "__main__":
    unittest.main()
