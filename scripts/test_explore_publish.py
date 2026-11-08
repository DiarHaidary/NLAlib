"""Publication must use the current main commit after its complete CI has passed."""
import copy
import unittest

from explore_publish import require_publishable


class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.sha = "a" * 40
        self.repo = "NLA-lib/NLAlib"
        self.run = {"id": 42, "name": "CI", "event": "push", "head_branch": "main",
                    "head_sha": self.sha, "status": "completed", "conclusion": "success",
                    "head_repository": {"full_name": self.repo}, "run_attempt": 1}
        self.head = self.sha
        self.runs = [self.run]

    def api(self, endpoint):
        if endpoint == f"repos/{self.repo}/git/ref/heads/main":
            return {"object": {"sha": self.head}}
        self.assertEqual(endpoint, f"repos/{self.repo}/actions/workflows/ci.yml/runs"
                         f"?branch=main&event=push&head_sha={self.sha}&per_page=100")
        return {"workflow_runs": self.runs}

    def check(self, name="workflow_run", ref="refs/heads/main", run=None):
        return require_publishable(name, {"workflow_run": run or self.run}, ref,
                                   self.sha, self.repo, self.api)

    def test_successful_main_ci_and_manual_retry(self):
        self.assertEqual(self.check(), 42)
        self.assertEqual(self.check("workflow_dispatch"), 42)

    def test_manual_feature_branch_or_tag_is_rejected(self):
        for ref in ("refs/heads/feature", "refs/tags/main"):
            with self.subTest(ref=ref), self.assertRaisesRegex(ValueError, "restricted to main"):
                self.check("workflow_dispatch", ref)

    def test_untrusted_or_unsuccessful_trigger_is_rejected(self):
        for key, value in (("name", "Other CI"), ("event", "pull_request"),
                           ("head_branch", "feature"), ("head_sha", "b" * 40),
                           ("status", "in_progress"), ("conclusion", "failure"),
                           ("head_repository", {"full_name": "fork/NLAlib"})):
            run = copy.deepcopy(self.run)
            run[key] = value
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, "successful push CI"):
                self.check(run=run)

    def test_main_advancing_during_extraction_blocks_upload(self):
        self.assertEqual(self.check(), 42)
        self.head = "b" * 40
        with self.assertRaisesRegex(ValueError, "no longer the head"):
            self.check()

    def test_missing_or_unrelated_ci_cannot_authorize_manual_publication(self):
        for runs in ([], [dict(self.run, head_sha="b" * 40)],
                     [dict(self.run, event="pull_request")],
                     [dict(self.run, head_branch="feature")],
                     [dict(self.run, head_repository={"full_name": "fork/NLAlib"})]):
            self.runs = runs
            with self.subTest(runs=runs), self.assertRaisesRegex(ValueError, "no main-branch CI"):
                self.check("workflow_dispatch")

    def test_newer_failed_or_running_ci_is_not_hidden_by_old_success(self):
        for status, conclusion in (("completed", "failure"), ("in_progress", None),
                                   ("completed", "cancelled"), ("completed", "skipped")):
            self.runs = [self.run, dict(self.run, id=43, status=status, conclusion=conclusion)]
            with self.subTest(status=status, conclusion=conclusion):
                with self.assertRaisesRegex(ValueError, "latest CI run"):
                    self.check("workflow_dispatch")

    def test_failed_rerun_of_same_run_blocks_publication(self):
        self.runs = [dict(self.run, run_attempt=2, conclusion="failure")]
        with self.assertRaisesRegex(ValueError, "latest CI run"):
            self.check()

    def test_unexpected_event_and_api_errors_fail_closed(self):
        with self.assertRaisesRegex(ValueError, "unsupported"):
            self.check("push")
        def unavailable(_):
            raise RuntimeError("API unavailable")
        with self.assertRaisesRegex(RuntimeError, "unavailable"):
            require_publishable("workflow_dispatch", {}, "refs/heads/main", self.sha,
                                self.repo, unavailable)


if __name__ == "__main__":
    unittest.main()
