import importlib.util
from datetime import datetime, timezone


def load_module():
    spec = importlib.util.spec_from_file_location(
        "check_pr", "ci/scripts/check-pr-changes-allowed.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_approval_after_commit_allows_change():
    mod = load_module()
    committers = {"alice": "Alice Example"}
    # last commit at noon
    last_commit_time = datetime.fromisoformat("2026-05-21T12:00:00+00:00")

    # approval submitted after last commit
    reviews = [("alice", "CHANGE AUTHORIZED: some/blocked/file.c", "APPROVED",
                "2026-05-21T12:30:00Z")]

    comments = []

    auth = mod.get_authorized_changes(comments, reviews, committers, last_commit_time)
    assert "some/blocked/file.c" in auth
    assert "alice" in auth["some/blocked/file.c"]


def test_approval_before_commit_is_stale():
    mod = load_module()
    committers = {"alice": "Alice Example"}
    # last commit at 13:00
    last_commit_time = datetime.fromisoformat("2026-05-21T13:00:00+00:00")

    # approval submitted before last commit
    reviews = [("alice", "CHANGE AUTHORIZED: some/blocked/file.c", "APPROVED",
                "2026-05-21T12:30:00Z")]

    comments = []

    auth = mod.get_authorized_changes(comments, reviews, committers, last_commit_time)
    assert "some/blocked/file.c" not in auth
