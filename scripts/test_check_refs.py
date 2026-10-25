#!/usr/bin/env python3
"""Focused regressions for standalone documentation tags."""
import unittest

from check_refs import ROOT, pair_has_result, same_module_path, tag_format_problems


class TagFormatTests(unittest.TestCase):
    def test_asymptotic_pair_requires_result_id(self):
        plain = '/-- A result. -/'
        tagged = '/-- A result.\nResult: valid-id -/'
        self.assertFalse(pair_has_result(plain, plain))
        self.assertTrue(pair_has_result(plain, tagged))
        self.assertTrue(pair_has_result(tagged, plain))

    def test_result_on_final_line(self):
        self.assertEqual(tag_format_problems('/-- A result.\nResult: first-id, second-id -/'), [])

    def test_inline_result(self):
        self.assertIn('inline `Result:` tag', tag_format_problems('/-- A result. Result: valid-id -/'))

    def test_empty_and_malformed_result(self):
        for value in ('', 'Bad_ID', 'good-id,', 'good-id extra'):
            with self.subTest(value=value):
                self.assertIn('malformed `Result:` tag',
                              tag_format_problems(f'/-- A result.\nResult: {value} -/'))

    def test_result_must_be_last(self):
        self.assertTrue(tag_format_problems('/-- A result.\nResult: good-id\nMore text. -/'))

    def test_asymptotic_formats(self):
        for tag in ('Asymptotic: NLAlib.explicit', 'Asymptotic:\nNLAlib.explicit'):
            with self.subTest(tag=tag):
                self.assertEqual(tag_format_problems(f'/-- A result.\n{tag}\nResult: good-id -/'), [])

    def test_inline_and_malformed_asymptotic(self):
        for tag in ('Text. Asymptotic: NLAlib.explicit', 'Asymptotic: two names',
                    'Asymptotic:', 'Asymptotic: `NLAlib.explicit`'):
            with self.subTest(tag=tag):
                self.assertTrue(tag_format_problems(f'/-- A result.\n{tag} -/'))


class SameFileTests(unittest.TestCase):
    def test_scaffold_and_library_file_of_one_path(self):
        lib, sc = ROOT / 'NLAlib' / 'A' / 'B.lean', ROOT / 'NLAlibScaffold' / 'A' / 'B.lean'
        self.assertTrue(same_module_path(sc, lib))
        self.assertTrue(same_module_path(lib, lib))
        self.assertFalse(same_module_path(sc, ROOT / 'NLAlib' / 'A' / 'C.lean'))


if __name__ == '__main__':
    unittest.main()
