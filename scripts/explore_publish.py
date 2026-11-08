#!/usr/bin/env python3
"""Require successful main-branch CI for the exact explorer publication commit.

Called both before extraction and immediately before uploading the rolling release.
This checks GitHub's live state; a delayed run cannot replace newer main-branch data.
"""
import json
import os
from pathlib import Path
import re
import subprocess


def require_publishable(event_name, event, ref, sha, repository, read_api):
    """Fail closed unless this event and the latest CI run authorize this main SHA."""
    if not re.fullmatch(r"[0-9a-f]{40}", sha):
        raise ValueError("publication requires a full commit SHA")
    if not re.fullmatch(r"[\w.-]+/[\w.-]+", repository):
        raise ValueError("invalid repository")
    if event_name == "workflow_dispatch":
        if ref != "refs/heads/main":
            raise ValueError("manual publication is restricted to main")
    elif event_name == "workflow_run":
        run = event.get("workflow_run", {})
        if (run.get("name") != "CI" or run.get("event") != "push"
                or run.get("head_branch") != "main" or run.get("head_sha") != sha
                or run.get("status") != "completed" or run.get("conclusion") != "success"
                or run.get("head_repository", {}).get("full_name") != repository):
            raise ValueError("publication requires successful push CI from this repository's main")
    else:
        raise ValueError("unsupported publication event")

    base = f"repos/{repository}"
    if read_api(f"{base}/git/ref/heads/main")["object"]["sha"] != sha:
        raise ValueError("publication commit is no longer the head of main")
    # Do not filter by success: a newer failed or running rerun must not be hidden.
    runs = read_api(f"{base}/actions/workflows/ci.yml/runs"
                    f"?branch=main&event=push&head_sha={sha}&per_page=100")["workflow_runs"]
    matching = [run for run in runs if run.get("head_sha") == sha
                and run.get("head_branch") == "main" and run.get("event") == "push"
                and run.get("head_repository", {}).get("full_name") == repository]
    if not matching:
        raise ValueError("no main-branch CI run exists for the publication commit")
    latest = max(matching, key=lambda run: (run["id"], run.get("run_attempt", 1)))
    if latest.get("status") != "completed" or latest.get("conclusion") != "success":
        raise ValueError("the latest CI run for this commit has not passed")
    return latest["id"]


def github_api(endpoint):
    result = subprocess.run(["gh", "api", endpoint], check=True, capture_output=True, text=True)
    return json.loads(result.stdout)


def main():
    sha = os.environ["SOURCE_SHA"]
    event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text(encoding="utf-8"))
    run_id = require_publishable(os.environ["GITHUB_EVENT_NAME"], event,
                                os.environ["GITHUB_REF"], sha,
                                os.environ["GITHUB_REPOSITORY"], github_api)
    print(f"Publication verified: main at {sha}, successful CI run {run_id}")


if __name__ == "__main__":
    main()
