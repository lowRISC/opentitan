# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Efficiently bisect FPGA regressions with the bitstream cache.

This tool bisects while minimizing the number of calls to the slow command.
Under the hood, it actually runs up to two git bisects. The first bisect only
tests commits that have cached bitstreams. The optional second bisect narrows
down ambiguous results. (For more information on bisecting, see `man 1
git-bisect` or <https://git-scm.com/docs/git-bisect>.)

In the first phase, the tool classifies commits as good/bad/skip with the
user-provided `--fast-command`. In the second phase, it uses `--slow-command`.
These commands classify the current commit via their exit status. Exiting with 0
indicates that the commit is good. Exiting with 125 indicates the commit cannot
be tested. Exiting with any other status indicates that the commit is bad.

Run bitstream_bisect.py with Bazel like so:

./bazelisk.sh run //util/fpga:bitstream_bisect -- \
    --good HEAD~30 \
    --bad HEAD \
    --fast-command "./bazelisk.sh test //sw/device/tests:uart_smoketest_fpga_cw310_rom" \
    --slow-command "./bazelisk.sh test --define bitstream=vivado \
        //sw/device/tests:uart_smoketest_fpga_cw310_rom"

"""

import abc
import enum
import os
import re
import shlex
import string
import subprocess
from typing import Dict, List, Optional, Set, Tuple

import rich
import rich.console
import typer

from rules.scripts.bitstreams_workspace import BitstreamCache


class CommitHash(str):
    """A string representation of a Git commit hash.

    The given string must contain only hex digits. It is canonicalized to
    lowercase, but not canonicalized relative to the current git repository. As
    such, two CommitHash objects may fail to compare equal even though git would
    say they refer to the same commit.
    """

    def __new__(cls, s):
        t = super().__new__(cls, s).lower()
        if len(t) == 0 or len(set(t) - set(string.hexdigits)) > 0:
            raise Exception("Invalid CommitHash input: '{}'".format(t))
        return t


class CommitJudgment(enum.Enum):
    GOOD = enum.auto()
    BAD = enum.auto()
    SKIP = enum.auto()


class BisectLog:
    """A container and parser for the results of `git bisect log`.
    """

    class ParserBug(Exception):
        pass

    def __init__(self, log: str):
        """Parse `log` and initialize the object."""
        lines = [s.rstrip() for s in log.splitlines()]
        self.judgments = BisectLog._extract_judgments(lines)
        self.candidates = BisectLog._extract_candidates(lines)

    @staticmethod
    def _extract_judgments(
            lines: List[str]) -> List[Tuple[CommitHash, CommitJudgment]]:
        out = []
        for line in lines:
            if line == '' or line.startswith("#"):
                continue
            if line == 'git bisect start':
                continue
            match = re.match("^git bisect (good|bad|skip) ([0-9a-f]+)$", line)
            if match is None:
                raise BisectLog.ParserBug(
                    "Failed to parse line: '{}'".format(line))
            assert len(match.groups()) == 2
            judgment, commit = match.groups()
            if judgment == 'good':
                out.append((CommitHash(commit), CommitJudgment.GOOD))
            elif judgment == 'bad':
                out.append((CommitHash(commit), CommitJudgment.BAD))
            elif judgment == 'skip':
                out.append((CommitHash(commit), CommitJudgment.SKIP))
            else:
                raise BisectLog.ParserBug("Unreachable")
        return out

    @staticmethod
    def _extract_candidates(lines: List[str]) -> List[CommitHash]:
        # Scan through the log to find a line indicating that there is a single
        # first bad commit.
        re_first_bad = re.compile(r"^# first bad commit: \[([0-9a-f]+)\] .*$")
        for i, line in enumerate(lines):
            match = re_first_bad.match(line)
            if match is None:
                continue
            assert len(match.groups()) == 1
            first_bad = match.group(1)
            return [CommitHash(first_bad)]

        # Scan through the log to find a sequence of possible first bad commits.
        LOG_LINE_ONLY_SKIPPED = "# only skipped commits left to test"
        candidate_lines = []
        for i, line in reversed(list(enumerate(lines))):
            # When only skipped commits remain, expect a sequence of "possible
            # first bad commit" lines.
            if line == LOG_LINE_ONLY_SKIPPED:
                candidate_lines = lines[i + 1:]
                break

        re_possible_first_bad = re.compile(
            r"^# possible first bad commit: \[([0-9a-f]+)\] .*$")
        candidates = []
        for line in candidate_lines:
            match = re_possible_first_bad.match(line)
            if match is None:
                continue
            assert len(match.groups()) == 1
            commit = match.group(1)
            candidates.append(CommitHash(commit))
        return candidates


class GitControllerABC(abc.ABC):
    """An abstract Git interface that will never run the system `git`."""

    @abc.abstractmethod
    def _git(self, *args: str) -> Tuple[int, str, str]:
        """Runs git with `args`. Returns (returncode, stdout, stderr)."""
        pass

    @abc.abstractmethod
    def _git_no_capture_output(self, *args: str) -> int:
        """Like `_git()`, but doesn't capture stdout/stderr."""
        pass

    def _git_checked(self, *args: str) -> Tuple[str, str]:
        """Like _git(), but raises an exception when the returncode != 0."""
        returncode, stdout, stderr = self._git(*args)
        if returncode != 0:
            lines = [
                "Git exited with {}".format(returncode),
                "---stdout---",
                stdout,
                "---stderr---",
                stderr,
            ]
            raise Exception("\n".join(lines))
        return (stdout, stderr)

    def rev_parse(self, commitish: str) -> CommitHash:
        stdout, _ = self._git_checked("rev-parse", commitish)
        return CommitHash(stdout.rstrip())

    def bisect_start(self):
        self._git_checked("bisect", "start")

    def bisect_reset(self):
        self._git_checked("bisect", "reset")

    def bisect_good(self, rev: CommitHash):
        self._git_checked("bisect", "good", rev)

    def bisect_bad(self, rev: CommitHash):
        self._git_checked("bisect", "bad", rev)

    def bisect_skip(self, rev: CommitHash):
        self._git_checked("bisect", "skip", rev)

    def bisect_run(self, *args: str) -> BisectLog:
        """Executes `git bisect run` without capturing stdout/stderr."""
        # Git's exit status is non-zero when bisect results are ambiguous.
        _ = self._git_no_capture_output("bisect", "run", *args)
        return self.bisect_log()

    def bisect_log(self) -> BisectLog:
        stdout, _ = self._git_checked("bisect", "log")
        return BisectLog(stdout)

    def bisect_view(self) -> List[Tuple[CommitHash, str]]:
        stdout, _ = self._git_checked("bisect", "view", "--oneline",
                                      "--no-abbrev-commit")
        out = []
        for line in stdout.splitlines():
            commit, tail = line.split(" ", 1)
            out.append((CommitHash(commit), tail))
        return out


class GitController(GitControllerABC):
    """A concrete git controller that actually executes git commands."""

    def __init__(self, git_binary: str, verbose: bool):
        self._git_binary = git_binary
        self._verbose = verbose
        self._console = rich.console.Console()
        self._env: Dict[str, str] = dict(os.environ)
        # Prevent `git bisect view` from launching the `gitk` GUI.
        self._env.pop("DISPLAY", None)

    def _git(self, *args: str) -> Tuple[int, str, str]:
        command = [self._git_binary] + list(args)
        proc = subprocess.run(command,
                              stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE,
                              env=self._env,
                              encoding="utf-8")
        if self._verbose or proc.returncode != 0:
            print()
            command_str = " ".join(command)
            rich.print(
                "Command [green]{}[/green] exited with status {}".format(
                    rich.markup.escape(command_str), proc.returncode))
            rich.print(
                rich.panel.Panel(rich.markup.escape(proc.stdout),
                                 title="git stdout"))
            rich.print(
                rich.panel.Panel(rich.markup.escape(proc.stderr),
                                 title="git stderr"))
        return (proc.returncode, proc.stdout, proc.stderr)

    def _git_no_capture_output(self, *args: str) -> int:
        command = [self._git_binary] + list(args)
        command_str = " ".join(command)
        command_str = rich.markup.escape(command_str)
        self._console.rule(
            "Streaming output from [bold]{}".format(command_str))
        proc = subprocess.run(["git"] + list(args), env=self._env)
        self._console.rule("Git exited with status {}".format(proc.returncode))
        self._console.print()
        return proc.returncode


class BisectSession:

    def __init__(self,
                 git: GitControllerABC,
                 cache_keys: Set[CommitHash],
                 visualize: bool = False):
        self._git = git
        self._cache_keys: Set[CommitHash] = cache_keys
        self._console = rich.console.Console()
        self._visualize = visualize

    def run(self,
            good_commit: CommitHash,
            bad_commit: CommitHash,
            fast_command: List[str],
            slow_command: Optional[List[str]] = None) -> BisectLog:
        """Run an unattended bisect session in one or two phases.

        This method is conceptually equivalent to `git bisect run`. Unlike plain
        `git bisect`, it runs in two phases. The first phase only operates on
        cached bitstreams. This will only get us so far, so it optionally can
        fall back to a slower command, e.g. one that builds the bitstreams it
        tests.

        Args:
          good_commit:
            Commit where `fast_command` and `slow_command` are known to succeed.
          bad_commit:
            Commit where `fast_command` and `slow_command` are known to fail.
          fast_command:
            A list of strings that represent a git-bisect script and args. These
            are passed to `git bisect run` in the first phase.
          slow_command:
            Just like `fast_command`, but for the second phase.  If this arg is
            None, we skip the second phase.

        Returns:
          Parsed output from `git bisect log`, run after the final bisect phase.
        """

        self._git.bisect_start()
        self._git.bisect_good(good_commit)
        self._git.bisect_bad(bad_commit)

        # Skip commits that aren't in the bitstream cache.
        for commit, _ in self._git.bisect_view():
            if commit not in self._cache_keys:
                self._git.bisect_skip(commit)

        self._maybe_visualize("Only testing commits with cached bitstreams")
        bisect_log = self._git.bisect_run(*fast_command)

        # Skip the second phase when results are unambiguous.
        if len(bisect_log.candidates) == 1:
            self._maybe_visualize("Final results")
            self._git.bisect_reset()
            return bisect_log

        # Prepare a new git bisect session where we will run the slow script
        # without the benefit of the bitstream cache. Replay all the "good" and
        # "bad" commands, but none of the "skip" commands.
        if slow_command is None:
            self._git.bisect_reset()
            return bisect_log

        self._git.bisect_reset()
        self._git.bisect_start()

        # Replay only "good" and "bad" decisions from the previous phase. It's
        # tempting to unconditionally skip cached commits, but it's better to
        # simply reuse judgments from the previous phase. It's possible that the
        # user-supplied `fast_command` chose to skip some cached commits for
        # reasons outside the scope of this tool, and we now need to test them
        # in the second phase.
        for commit, judgment in bisect_log.judgments:
            if judgment == CommitJudgment.GOOD:
                self._git.bisect_good(commit)
            elif judgment == CommitJudgment.BAD:
                self._git.bisect_bad(commit)

        self._maybe_visualize("Narrowing down ambiguous results")
        bisect_log = self._git.bisect_run(*slow_command)

        self._maybe_visualize("Final results")
        self._git.bisect_reset()
        return bisect_log

    def _maybe_visualize(self, label: str):
        """Prints a table summarizing the current range of commits."""
        if not self._visualize:
            return

        table = rich.table.Table(
            title="Bitstream Bisect Status: [bold]{}".format(label))
        table.add_column("Commit")
        table.add_column("Description")
        table.add_column("Cached")
        table.add_column("Judgment")

        bisect_log = self._git.bisect_log()
        judgment_dict: Dict[CommitHash,
                            CommitJudgment] = dict(bisect_log.judgments)

        for commit, description in self._git.bisect_view():
            judgment = judgment_dict.get(commit)
            table.add_row(commit, rich.markup.escape(description),
                          "Cached" if commit in self._cache_keys else "",
                          judgment.name if judgment else "")

        self._console.print(table)


app = typer.Typer(pretty_exceptions_enable=False,
                  rich_markup_mode="rich",
                  add_completion=False)


@app.command(help=__doc__)
def main(
    good: str = typer.Option(..., help="Commit-ish for known-good revision."),
    bad: str = typer.Option(..., help="Commit-ish for known-bad revision."),
    fast_command: str = typer.Option(
        ..., help="Command for testing commits with cached bitstreams."),
    slow_command: Optional[str] = typer.Option(
        None, help="Command that tests remaining commits in second phase."),
    git_binary: str = typer.Option("/usr/bin/git", help="Path to Git binary."),
    verbose: bool = typer.Option(
        False, help="Log stdout/stderr of every git command."),
):
    # Escape the Bazel sandbox. Without this step, git would not find the .git/
    # directory. Note that this works nicely with git worktrees.
    workspace_dir = os.environ['BUILD_WORKSPACE_DIRECTORY']
    os.chdir(workspace_dir)

    # Create a Git controller capable of invoking the system's `git` binary. Use
    # it to canonicalize potentially-symbolic "commitish" strings so we don't
    # misinterpret them when a different commit is checked out.
    git = GitController(git_binary, verbose)
    good_commit = git.rev_parse(good)
    bad_commit = git.rev_parse(bad)
    print("Canonicalized good revision:", good_commit)
    print("Canonicalized bad revision: ", bad_commit)

    # NOTE: This will generate network traffic!
    # Fetch a listing of the current bitstream cache.
    bitstream_cache = BitstreamCache.MakeWithDefaults()
    bitstream_cache.GetBitstreamsAvailable(refresh=True)
    bitstream_cache_keys = set(bitstream_cache.available.keys())

    fast_command_pieces = shlex.split(fast_command)
    slow_command_pieces = shlex.split(
        slow_command) if slow_command is not None else None

    session = BisectSession(git, bitstream_cache_keys, visualize=True)
    session.run(good_commit,
                bad_commit,
                fast_command_pieces,
                slow_command=slow_command_pieces)
    return 0


if __name__ == '__main__':
    app()
