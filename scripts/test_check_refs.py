#!/usr/bin/env python3
"""Focused regressions for standalone documentation tags."""
import unittest

from check_refs import algorithm_tag_problems, pair_has_result, tag_format_problems


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



class AlgorithmTagTests(unittest.TestCase):
    def rules(self, doc, kind='def'):
        return [rid for rid, _ in algorithm_tag_problems(doc, kind)]

    def test_well_formed(self):
        for tag in ('Algorithm: cg', 'Algorithm: randomized-svd', 'Algorithm: cg (specification)',
                    'Algorithm: lanczos (run model)'):
            with self.subTest(tag=tag):
                self.assertEqual(self.rules(f'/-- **A def.** Text.\n{tag} -/'), [])
        self.assertEqual(self.rules('/-- A run.\nAlgorithm: lanczos -/', 'structure'), [])
        self.assertEqual(self.rules('/-- No tag; the word Algorithm alone. -/', 'theorem'), [])

    def test_malformed(self):
        for tag in ('Algorithm:', 'Algorithm: CG', 'Algorithm: cg_state', 'Algorithm: cg pcg',
                    'Algorithm: cg (program)', 'Algorithm: `cg`'):
            with self.subTest(tag=tag):
                self.assertEqual(self.rules(f'/-- A def.\n{tag} -/'), ['A1'])

    def test_inline_and_not_last(self):
        self.assertEqual(self.rules('/-- A def. Algorithm: cg -/'), ['A1'])
        self.assertEqual(self.rules('/-- A def.\nAlgorithm: cg\nMore text. -/'), ['A1'])

    def test_kinds(self):
        for kind in ('theorem', 'lemma', 'instance', None):
            with self.subTest(kind=kind):
                self.assertEqual(self.rules('/-- A result.\nAlgorithm: cg -/', kind), ['A2'])

    def test_at_most_one(self):
        self.assertIn('A3', self.rules('/-- A def.\nAlgorithm: cg\nAlgorithm: pcg -/'))


if __name__ == '__main__':
    unittest.main()
