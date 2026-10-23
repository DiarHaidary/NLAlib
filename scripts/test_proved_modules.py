#!/usr/bin/env python3
"""Regressions for the import and `sorry` scan of `scripts/proved_modules.py`."""
import unittest

from proved_modules import has_sorry, nlalib_imports


class ImportTests(unittest.TestCase):
    def test_every_import_form(self):
        text = "\n".join([
            "module",
            "",
            "public import NLAlib.A",
            "import NLAlib.B",
            "import all NLAlib.C",
            "public import all NLAlib.D",
            "meta import NLAlib.E",
            "public meta import NLAlib.F",
            "public import Mathlib.Data.Real.Basic",
            "import all Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss",
        ])
        self.assertEqual(nlalib_imports(text),
                         ["NLAlib.A", "NLAlib.B", "NLAlib.C", "NLAlib.D", "NLAlib.E", "NLAlib.F"])

    def test_indented_or_quoted_import_is_not_an_import(self):
        self.assertEqual(nlalib_imports("  import NLAlib.A\n-- see `import NLAlib.B`"), [])

    def test_sorry_outside_comments_only(self):
        self.assertTrue(has_sorry("theorem t : True := by sorry"))
        self.assertFalse(has_sorry("/- sorry -/\n-- sorry\ntheorem t : True := trivial"))
        self.assertFalse(has_sorry("theorem sorryFree : True := trivial"))


if __name__ == "__main__":
    unittest.main()
