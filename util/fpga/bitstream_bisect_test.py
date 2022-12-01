# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import unittest
from typing import Tuple
from unittest.mock import MagicMock, call

from bitstream_bisect import (BisectLog, BisectSession, CommitHash,
                              CommitJudgment, GitControllerABC)


class MockableGitController(GitControllerABC):
    """Provides stub implementations of GitControllerABC's abstract methods."""

    def _git(self, *args: str) -> Tuple[int, str, str]:
        raise Exception("_git unexpectedly called")

    def _git_no_capture_output(self, *args: str) -> int:
        returncode, _, _ = self._git(*args)
        return returncode


class TestCommitHash(unittest.TestCase):
    """Test that CommitHash validates its inputs."""

    def test_simple(self):
        c = CommitHash("c1")
        self.assertEqual(str(c), "c1")

        c = CommitHash("deadbeef")
        self.assertEqual(str(c), "deadbeef")
        self.assertEqual(str(c), CommitHash("deadbeef"))

    def test_non_lowercase(self):
        c = CommitHash("C1")
        self.assertEqual(str(c), "c1")
        self.assertEqual(str(c), CommitHash("C1"))
        self.assertEqual(str(c), CommitHash("c1"))

        c = CommitHash("DEADBEEF")
        self.assertEqual(str(c), "deadbeef")
        self.assertEqual(str(c), CommitHash("DEADBEEF"))
        self.assertEqual(str(c), CommitHash("deadbeef"))

        c = CommitHash("DeAdBeEf")
        self.assertEqual(str(c), "deadbeef")
        self.assertEqual(str(c), CommitHash("DeAdBeEf"))
        self.assertEqual(str(c), CommitHash("deadbeef"))

    def test_invalid(self):
        with self.assertRaises(Exception):
            CommitHash("")
        with self.assertRaises(Exception):
            CommitHash("hello")
        with self.assertRaises(Exception):
            CommitHash("HEAD")


class TestParseBisectLog(unittest.TestCase):

    def test_one_line(self):
        bisect_log = BisectLog("git bisect good c123")
        self.assertEqual(bisect_log.judgments, [('c123', CommitJudgment.GOOD)])
        self.assertEqual(bisect_log.candidates, [])

        bisect_log = BisectLog("git bisect bad c123")
        self.assertEqual(bisect_log.judgments, [('c123', CommitJudgment.BAD)])
        self.assertEqual(bisect_log.candidates, [])

        bisect_log = BisectLog("git bisect skip c123")
        self.assertEqual(bisect_log.judgments, [('c123', CommitJudgment.SKIP)])
        self.assertEqual(bisect_log.candidates, [])

        bisect_log = BisectLog("")
        self.assertEqual(bisect_log.judgments, [])
        self.assertEqual(bisect_log.candidates, [])

        bisect_log = BisectLog("git bisect start")
        self.assertEqual(bisect_log.judgments, [])
        self.assertEqual(bisect_log.candidates, [])

    def test_unrecognized_actions_rejected(self):
        """The parser should reject non-comment lines it doesn't understand."""
        # Unexpected whitespace.
        with self.assertRaises(BisectLog.ParserBug):
            _ = BisectLog(" git bisect skip c123")
        with self.assertRaises(BisectLog.ParserBug):
            _ = BisectLog("git  bisect skip c123")
        with self.assertRaises(BisectLog.ParserBug):
            _ = BisectLog("git bisect  skip c123")
        with self.assertRaises(BisectLog.ParserBug):
            _ = BisectLog(" # git bisect  skip c123")
        # Unrecognized action with commit.
        with self.assertRaises(BisectLog.ParserBug):
            _ = BisectLog("git bisect foo c123")
        # Unrecognized action without commit.
        with self.assertRaises(BisectLog.ParserBug):
            _ = BisectLog("git bisect bar")

    def test_unrecognized_comments_ignored(self):
        bisect_log = BisectLog("# foo")
        self.assertEqual(bisect_log.judgments, [])
        self.assertEqual(bisect_log.candidates, [])

    def test_candidates_simple(self):
        bisect_log = BisectLog("")
        self.assertEqual(bisect_log.judgments, [])
        self.assertEqual(bisect_log.candidates, [])

        bisect_log = BisectLog(
            "# first bad commit: [c42] Commit description...")
        self.assertEqual(bisect_log.judgments, [])
        self.assertEqual(bisect_log.candidates, ["c42"])

        bisect_log = BisectLog("""
# only skipped commits left to test
# possible first bad commit: [c123] Foo description
# possible first bad commit: [c234] Bar description
""")
        self.assertEqual(bisect_log.judgments, [])
        self.assertEqual(bisect_log.candidates, ["c123", "c234"])

    def test_realistic_only_skipped_remain(self):
        # This output was produced by `git` on a temporary repo.
        BISECT_LOG = """# status: waiting for both good and bad commits
# good: [0b47ff5f2ac78589cab7d9b93c4cabb9e4a1f736] First commit
git bisect good 0b47ff5f2ac78589cab7d9b93c4cabb9e4a1f736
# status: waiting for bad commit, 1 good commit known
# bad: [4f166216806f44b1ddf67c4649d5e646cf9bbf22] Fourth commit
git bisect bad 4f166216806f44b1ddf67c4649d5e646cf9bbf22
# skip: [132c4e1f8773cd3e14e2f4de8a8b77422b74e28b] Third commit
git bisect skip 132c4e1f8773cd3e14e2f4de8a8b77422b74e28b
# skip: [8fe76ab59c4f7d43237292a57f1d84b774436224] Second commit
git bisect skip 8fe76ab59c4f7d43237292a57f1d84b774436224
# only skipped commits left to test
# possible first bad commit: [4f166216806f44b1ddf67c4649d5e646cf9bbf22] Fourth commit
# possible first bad commit: [132c4e1f8773cd3e14e2f4de8a8b77422b74e28b] Third commit
# possible first bad commit: [8fe76ab59c4f7d43237292a57f1d84b774436224] Second commit
# good: [8fe76ab59c4f7d43237292a57f1d84b774436224] Second commit
git bisect good 8fe76ab59c4f7d43237292a57f1d84b774436224
# only skipped commits left to test
# possible first bad commit: [4f166216806f44b1ddf67c4649d5e646cf9bbf22] Fourth commit
# possible first bad commit: [132c4e1f8773cd3e14e2f4de8a8b77422b74e28b] Third commit
"""
        bisect_log = BisectLog(BISECT_LOG)
        self.assertEqual(bisect_log.candidates, [
            "4f166216806f44b1ddf67c4649d5e646cf9bbf22",
            "132c4e1f8773cd3e14e2f4de8a8b77422b74e28b"
        ])
        self.assertEqual(bisect_log.judgments, [
            ("0b47ff5f2ac78589cab7d9b93c4cabb9e4a1f736", CommitJudgment.GOOD),
            ("4f166216806f44b1ddf67c4649d5e646cf9bbf22", CommitJudgment.BAD),
            ("132c4e1f8773cd3e14e2f4de8a8b77422b74e28b", CommitJudgment.SKIP),
            ("8fe76ab59c4f7d43237292a57f1d84b774436224", CommitJudgment.SKIP),
            ("8fe76ab59c4f7d43237292a57f1d84b774436224", CommitJudgment.GOOD),
        ])

    def test_realistic_has_first_bad_commit(self):
        # This output was produced by `git` on a temporary repo.
        BISECT_LOG = """git bisect start
# status: waiting for both good and bad commits
# good: [00722da469712cd917e59082601d189fe0c6507e] First commit
git bisect good 00722da469712cd917e59082601d189fe0c6507e
# status: waiting for bad commit, 1 good commit known
# bad: [3e2031c1cb7b27e8bf36c85756c301279b8f9f30] Fourth commit
git bisect bad 3e2031c1cb7b27e8bf36c85756c301279b8f9f30
# bad: [dc5320f6d974d3fce7bcc03fd18d920c8b5e3cbf] Third commit
git bisect bad dc5320f6d974d3fce7bcc03fd18d920c8b5e3cbf
# bad: [d72b7491e6fdadb2ef742370410d5488a7bbfdba] Second commit
git bisect bad d72b7491e6fdadb2ef742370410d5488a7bbfdba
# first bad commit: [d72b7491e6fdadb2ef742370410d5488a7bbfdba] Second commit
"""
        bisect_log = BisectLog(BISECT_LOG)
        self.assertEqual(bisect_log.candidates,
                         ["d72b7491e6fdadb2ef742370410d5488a7bbfdba"])
        self.assertEqual(bisect_log.judgments, [
            ("00722da469712cd917e59082601d189fe0c6507e", CommitJudgment.GOOD),
            ("3e2031c1cb7b27e8bf36c85756c301279b8f9f30", CommitJudgment.BAD),
            ("dc5320f6d974d3fce7bcc03fd18d920c8b5e3cbf", CommitJudgment.BAD),
            ("d72b7491e6fdadb2ef742370410d5488a7bbfdba", CommitJudgment.BAD),
        ])


class TestBisectSession(unittest.TestCase):

    def test_two_cached_only_fast(self):
        """Simple case with two cached commits and only the fast command."""

        BISECT_LOG = """git bisect start
# status: waiting for both good and bad commits
# good: [c1] Fake good commit
git bisect good c1
# status: waiting for bad commit, 1 good commit known
# bad: [c2] Fake bad commit
git bisect bad c2
# first bad commit: [c2] Fake bad commit
"""

        git = MockableGitController()
        git._git = MagicMock(return_value=(0, "", ""))
        git.bisect_view = MagicMock(return_value=[
            (CommitHash("c1"), "Commit description"),
            (CommitHash("c2"), "Commit description"),
        ])
        git.bisect_log = MagicMock(return_value=BisectLog(BISECT_LOG))

        session = BisectSession(git, cache_keys=set(["c1", "c2"]))
        result: BisectLog = session.run("c1", "c2", ["fast_script.sh"])

        self.assertEqual(result.candidates, ["c2"])
        git._git.assert_has_calls([
            call("bisect", "start"),
            call("bisect", "good", "c1"),
            call("bisect", "bad", "c2"),
            call('bisect', 'run', 'fast_script.sh'),
            # We would expect `call('bisect', 'log')` here, but mocking
            # `git.bisect_log()` prevented it from calling `git._git()`.
            call('bisect', 'reset'),
        ])
        git.bisect_log.assert_called_once_with()
        git.bisect_view.assert_called_once_with()

    def test_only_fast(self):
        """Mix of cached and uncached with only the fast command."""

        BISECT_LOG = """git bisect start
# status: waiting for both good and bad commits
# skip: [c2] Skipped commit
git bisect skip c2
# good: [c1] Fake good commit
git bisect good c1
# status: waiting for bad commit, 1 good commit known
# bad: [c3] Fake bad commit
git bisect bad c3
# only skipped commits left to test
# possible first bad commit: [c2] Skipped commit
# possible first bad commit: [c3] Fake bad commit
"""

        git = MockableGitController()
        git._git = MagicMock(return_value=(0, "", ""))
        git.bisect_view = MagicMock(return_value=[
            (CommitHash("c1"), "Fake good commit"),
            (CommitHash("c2"), "Skipped commit"),
            (CommitHash("c3"), "Fake bad commit"),
        ])

        git.bisect_log = MagicMock(return_value=BisectLog(BISECT_LOG))

        session = BisectSession(git, cache_keys=set(["c1", "c3"]))
        bisect_log = session.run("c1", "c3", ["fast_script.sh"])

        self.assertEqual(bisect_log.candidates, ["c2", "c3"])
        git._git.assert_has_calls([
            call("bisect", "start"),
            call("bisect", "good", "c1"),
            call("bisect", "bad", "c3"),
            call("bisect", "skip", "c2"),
            call('bisect', 'run', 'fast_script.sh'),
            # We would expect `call('bisect', 'log')` here, but mocking
            # `git.bisect_log()` prevented it from calling `git._git()`.
        ])
        git.bisect_log.assert_called_once_with()
        git.bisect_view.assert_called_once_with()

    def test_fast_and_slow(self):
        """Mix of cached and uncached with fast and slow command."""

        BISECT_LOG_1 = """git bisect start
# status: waiting for both good and bad commits
# good: [c1] Commit 1
git bisect good c1
# status: waiting for bad commit, 1 good commit known
# bad: [c5] Commit 5
git bisect bad c5
# skip: [c3] Commit 3
git bisect skip c3
# skip: [c4] Commit 4
git bisect skip c4
# good: [c2] Commit 2
git bisect good c2
# only skipped commits left to test
# possible first bad commit: [c3] Commit 3
# possible first bad commit: [c4] Commit 4
"""
        BISECT_LOG_2 = """git bisect start
# status: waiting for both good and bad commits
# good: [c1] Commit 1
git bisect good c1
# status: waiting for bad commit, 1 good commit known
# bad: [c5] Commit 5
git bisect bad c5
# good: [c2] Commit 2
git bisect good c2
# good: [c3] Commit 3
git bisect good c3
# bad: [c4] Commit 4
git bisect bad c4
# first bad commit: [c4] Commit 4
"""
        parsed_bisect_logs = [BisectLog(BISECT_LOG_1), BisectLog(BISECT_LOG_2)]

        git = MockableGitController()
        git._git = MagicMock(return_value=(0, "", ""))
        git.bisect_log = MagicMock(side_effect=parsed_bisect_logs)

        git.bisect_view = MagicMock(return_value=[
            (CommitHash("c1"), "Commit 1"),
            (CommitHash("c2"), "Commit 2"),
            (CommitHash("c3"), "Commit 3"),
            (CommitHash("c4"), "Commit 4"),
            (CommitHash("c5"), "Commit 5"),
        ])

        session = BisectSession(git, cache_keys=set(["c1", "c2"]))
        bisect_log = session.run("c1", "c5", ["fast_script.sh"],
                                 ["slow_script.sh"])

        self.assertEqual(bisect_log.candidates, ["c4"])

        git._git.assert_has_calls([
            call("bisect", "start"),
            call("bisect", "good", "c1"),
            call("bisect", "bad", "c5"),
            call("bisect", "skip", "c3"),
            call("bisect", "skip", "c4"),
            call("bisect", "skip", "c5"),
            call('bisect', 'run', 'fast_script.sh'),
            call('bisect', 'reset'),
            call('bisect', 'start'),
            call('bisect', 'good', 'c1'),
            call('bisect', 'bad', 'c5'),
            call('bisect', 'good', 'c2'),
            call('bisect', 'run', 'slow_script.sh'),
        ])
        git.bisect_log.assert_has_calls([call(), call()])
        git.bisect_view.assert_called_once_with()


if __name__ == '__main__':
    unittest.main()
