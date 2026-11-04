#!/usr/bin/env python3
"""Regressions for complete bound bodies and Lean docstring boundaries, without a Lean build."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest

from check_constants import digest, docstrings, find_definition, run


FIXTURES = Path(__file__).parent / "fixtures" / "lean_docstrings.json"
BOUND = """/-- The value is <!-- value exampleBound -->$2$. -/
def exampleBound : Nat :=
  let x := 1

  x + 1
"""


def fixture_root(path, source=BOUND, registered=BOUND):
    root = Path(path)
    (root / "docs").mkdir()
    (root / "NLAlib").mkdir()
    (root / "NLAlib" / "Example.lean").write_text(source, encoding="utf-8")
    body = find_definition(registered, "exampleBound")[1]
    (root / "docs" / "constants.toml").write_text(
        '[[constant]]\nname = "NLAlib.exampleBound"\nkind = "bound"\n'
        'file = "NLAlib/Example.lean"\nargs = []\nlatex = "2"\n'
        f'lean_body = {json.dumps(body)}\nbody_hash = "{digest(body)}"\n', encoding="utf-8")
    return root


def check(root, update_names=()):
    output = io.StringIO()
    with contextlib.redirect_stdout(output):
        status = run(root, list(update_names))
    return status, output.getvalue()


class DocstringTests(unittest.TestCase):
    def test_shared_lean_lexical_cases(self):
        for fixture in json.loads(FIXTURES.read_text(encoding="utf-8")):
            with self.subTest(fixture["name"]):
                source = fixture["source"]
                self.assertEqual([source[a:b] for a, b in docstrings(source)], fixture["docs"])

    def test_value_after_nested_comment_is_checked(self):
        source = BOUND.replace("The value", "After `/- inner -/`, the value")
        with tempfile.TemporaryDirectory() as tmp:
            root = fixture_root(tmp, source)
            self.assertEqual(check(root)[0], 0)
            (root / "NLAlib" / "Example.lean").write_text(
                source.replace("$2$", "$101$"), encoding="utf-8")
            status, output = check(root)
            self.assertEqual(status, 1)
            self.assertIn("does not contain its value '2'", output)

    def test_string_opener_does_not_hide_missing_value(self):
        source = 'def opener := "/-"\n' + BOUND
        with tempfile.TemporaryDirectory() as tmp:
            root = fixture_root(tmp, source)
            self.assertEqual(check(root)[0], 0)
            (root / "NLAlib" / "Example.lean").write_text(
                source.replace("<!-- value exampleBound -->", ""), encoding="utf-8")
            status, output = check(root)
            self.assertEqual(status, 1)
            self.assertIn("must show its value", output)


class DefinitionTests(unittest.TestCase):
    def test_internal_blank_lines_preserve_entire_body(self):
        body = find_definition(BOUND, "exampleBound")[1]
        self.assertEqual(body, "exampleBound : Nat := let x := 1 x + 1")
        self.assertNotEqual(body, find_definition(BOUND.replace("x + 1", "x + 100"),
                                                "exampleBound")[1])

    def test_next_declaration_is_not_in_body(self):
        expected = find_definition(BOUND, "exampleBound")[1]
        for gap in ("", "\n", "\n  \n"):
            for following in ("def next := 3\n", "/-- Next. -/\ndef next := 3\n"):
                with self.subTest(gap=gap, following=following):
                    source = BOUND + gap + following
                    self.assertEqual(find_definition(source, "exampleBound")[1], expected)
                    self.assertEqual(find_definition(source.replace("next := 3", "next := 4"),
                                                     "exampleBound")[1], expected)

    def test_comments_inside_body_do_not_hide_suffix(self):
        for comment in ("-- explanation", "/- outer\n/- inner -/\n-/"):
            with self.subTest(comment=comment), tempfile.TemporaryDirectory() as tmp:
                source = BOUND.replace("\n\n  x + 1", f"\n\n{comment}\n  x + 1")
                root = fixture_root(tmp, source, source)
                self.assertEqual(check(root)[0], 0)
                self.assertTrue(find_definition(source, "exampleBound")[1].endswith("x + 1"))
                (root / "NLAlib" / "Example.lean").write_text(
                    source.replace("x + 1", "x + 100"), encoding="utf-8")
                status, output = check(root)
                self.assertEqual(status, 1)
                self.assertIn("the body of NLAlib.exampleBound changed", output)

    def test_declaration_continuations_are_hashed(self):
        cases = [
            ("def exampleBound : Nat := f 1\nwhere\n  f (x : Nat) := x + 1\n", "x + 1", "x + 100"),
            ("def exampleBound : Nat → Nat\n| 0 => 2\n| n + 1 => exampleBound n\n", "0 => 2", "0 => 3"),
            ("def exampleBound : Nat → Nat\n|0 => 2\n|n + 1 => exampleBound n\n", "0 => 2", "0 => 3"),
            ("def exampleBound : Nat → Nat\n| 0 => 2\n| n + 1 => exampleBound n\n"
             "termination_by n => n\n", "n => n", "n => n + 1"),
            ("def exampleBound : Nat → Nat\n| 0 => 2\n| n + 1 => exampleBound n\n"
             "termination_by n => n\ndecreasing_by\n  omega\n", "omega", "simp_wf; omega"),
        ]
        for declaration, before, after in cases:
            with self.subTest(declaration=declaration), tempfile.TemporaryDirectory() as tmp:
                source = BOUND.split("\ndef ")[0] + "\n" + declaration
                expected = find_definition(source, "exampleBound")[1]
                self.assertEqual(expected, " ".join(declaration.removeprefix("def ").split()))
                self.assertEqual(find_definition(source + "\ndef next := 3\n",
                                                 "exampleBound")[1], expected)
                root = fixture_root(tmp, source, source)
                self.assertEqual(check(root)[0], 0)
                (root / "NLAlib" / "Example.lean").write_text(
                    source.replace(before, after), encoding="utf-8")
                self.assertEqual(check(root)[0], 1)

    def test_literal_or_comment_cannot_supply_fake_definition(self):
        fake = "def exampleBound : Nat := 999"
        for prefix in (f"/-\n{fake}\n-/\n", f'def text := r#"\n{fake}\n"#\n'):
            with self.subTest(prefix=prefix):
                self.assertEqual(find_definition(prefix + BOUND, "exampleBound")[1],
                                 "exampleBound : Nat := let x := 1 x + 1")

    def test_multiline_literal_stays_in_body(self):
        source = 'def exampleBound := r#"first\n\nlast"#\n\ndef next := 3\n'
        self.assertEqual(find_definition(source, "exampleBound")[1],
                         'exampleBound := r#"first last"#')

    def test_indented_declaration_stops_at_its_own_level(self):
        source = "\n".join("  " + line for line in (BOUND + "def next := 3\n").split("\n"))
        self.assertEqual(find_definition(source, "exampleBound")[1],
                         "exampleBound : Nat := let x := 1 x + 1")

    def test_changed_suffix_is_rejected_by_full_checker(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = fixture_root(tmp)
            self.assertEqual(check(root)[0], 0)
            (root / "NLAlib" / "Example.lean").write_text(
                BOUND.replace("x + 1", "x + 100"), encoding="utf-8")
            status, output = check(root)
            self.assertEqual(status, 1)
            self.assertIn("the body of NLAlib.exampleBound changed", output)

    def test_next_declaration_change_does_not_stale_registry(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = fixture_root(tmp, BOUND + "\ndef next := 3\n")
            self.assertEqual(check(root)[0], 0)
            (root / "NLAlib" / "Example.lean").write_text(
                BOUND + "\ndef next := 100\n", encoding="utf-8")
            self.assertEqual(check(root)[0], 0)

    def test_update_records_complete_body_and_rewrites_value(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = fixture_root(tmp, BOUND.replace("x + 1", "x + 100"))
            registry = root / "docs" / "constants.toml"
            registry.write_text(registry.read_text(encoding="utf-8").replace(
                'latex = "2"', 'previous_latex = "2"\nlatex = "101"'), encoding="utf-8")
            self.assertEqual(check(root, ["exampleBound"])[0], 0)
            self.assertIn("x + 100", registry.read_text(encoding="utf-8"))
            self.assertIn("$101$", (root / "NLAlib" / "Example.lean").read_text(encoding="utf-8"))
            self.assertEqual(check(root)[0], 0)


if __name__ == "__main__":
    unittest.main()
