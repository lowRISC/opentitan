# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import os
import re
from pathlib import Path

from utils import VERBOSE, clean_odirs, rm_path


class LauncherError(Exception):
    def __init__(self, msg):
        self.msg = msg


class Launcher:
    """
    Abstraction for launching and maintaining a job.

    An abstract class that provides methods to prepare a job's environment,
    launch the job, poll for its completion and finally do some cleanup
    activities. This class is not meant to be instantiated directly. Each
    launcher object holds an instance of the deploy object.
    """

    # If a history of previous invocations is to be maintained, then keep no
    # more than this many directories.
    max_odirs = 5

    def __str__(self):
        return self.deploy.full_name + ":launcher"

    def __init__(self, deploy):
        # Store the deploy object handle.
        self.deploy = deploy

        # Return status of the process running the job.
        self.exit_code = None

        # Flag to indicate whether to 'overwrite' if odir already exists,
        # or to backup the existing one and create a new one.
        # For builds, we want to overwrite existing to leverage the tools'
        # incremental / partition compile features. For runs, we may want to
        # create a new one.
        self.renew_odir = False

        # Construct failure message if the test fails.
        self.fail_msg = "\n**{!r}:** {!r}<br>\n".format(
            self.deploy.target.upper(), self.deploy.qual_name)
        self.fail_msg += "**LOG:** {}<br>\n".format(self.deploy.get_log_path())

    def _make_odir(self):
        """Create the output directory."""

        # If renew_odir flag is True - then move it.
        if self.renew_odir:
            clean_odirs(odir=self.deploy.odir, max_odirs=self.max_odirs)
        os.makedirs(self.deploy.odir, exist_ok=True)

    def _dump_env_vars(self, exports):
        """Write env vars to a file for ease of debug.

        Each extended class computes the list of exports and invokes this
        method right before launching the job.
        """

        with open(self.deploy.odir + "/env_vars",
                  "w",
                  encoding="UTF-8",
                  errors="surrogateescape") as f:
            for var in sorted(exports.keys()):
                f.write("{}={}\n".format(var, exports[var]))

    def _pre_launch(self):
        """Do pre-launch activities.

        Examples include such as preparing the job's environment, clearing
        old runs, creating the output directory, dumping all env variables
        etc. This method is already invoked by launch() as the first step.
        """

        self.deploy.pre_launch()
        self._make_odir()

    def _do_launch(self):
        """Launch the job."""

        raise NotImplementedError()

    def launch(self):
        """Launch the job."""

        self._pre_launch()
        self._do_launch()

    def _post_finish(self, status):
        """Do post-completion activities, such as preparing the results.

        Must be invoked by poll().
        """

        assert status in ['P', 'F', 'K']
        if status in ['P', 'F']:
            self._link_odir(status)
        self.deploy.post_finish(status)
        log.debug("Item %s has completed execution: %s", self, status)

    def poll(self):
        """Poll the launched job for completion.

        Invokes _has_passed() and _post_finish() when the job completes.
        """

        raise NotImplementedError()

    def kill(self):
        """Terminate the job."""

        raise NotImplementedError()

    def _has_passed(self):
        """Determine the outcome of the job (P/F if it ran to completion).

        Return True if the job passed, False otherwise. This is called by
        poll() just after the job finishes.
        """
        def log_fail_msg(msg):
            """Logs the fail msg to the final report."""

            self.fail_msg += msg
            log.log(VERBOSE, msg)

        def _find_patterns(patterns, line):
            """Helper function that returns the pattern if any of the given
            patterns is found, else None."""

            assert patterns
            for pattern in patterns:
                match = re.search(r"{}".format(pattern), line)
                if match:
                    return pattern
            return None

        def _get_n_lines(pos, num):
            "Helper function that returns next N lines starting at pos index."

            return ''.join(lines[pos:pos + num - 1]).strip()

        if self.deploy.dry_run:
            return True

        # Only one fail pattern needs to be seen.
        failed = False
        chk_failed = bool(self.deploy.fail_patterns)

        # All pass patterns need to be seen, so we replicate the list and remove
        # patterns as we encounter them.
        pass_patterns = self.deploy.pass_patterns.copy()
        chk_passed = bool(pass_patterns) and (self.exit_code == 0)

        try:
            with open(self.deploy.get_log_path(), "r", encoding="UTF-8") as f:
                lines = f.readlines()
        except OSError as e:
            log_fail_msg("Error opening file {}:\n{}".format(
                self.deploy.get_log_path(), e))
            return False

        if chk_failed or chk_passed:
            for cnt, line in enumerate(lines):
                if chk_failed:
                    if _find_patterns(self.deploy.fail_patterns,
                                      line) is not None:
                        # Print 4 additional lines to help debug more easily.
                        log_fail_msg("```\n{}\n```\n".format(
                            _get_n_lines(cnt, 5)))
                        failed = True
                        chk_failed = False
                        chk_passed = False

                if chk_passed:
                    pattern = _find_patterns(pass_patterns, line)
                    if pattern is not None:
                        pass_patterns.remove(pattern)
                        chk_passed = bool(pass_patterns)

        # If failed, then nothing else to do. Just return.
        if failed:
            return False

        # If no fail patterns were seen, but the job returned with non-zero
        # exit code for whatever reason, then show the last 10 lines of the log
        # as the failure message, which might help with the debug.
        if self.exit_code != 0:
            msg = ''.join(lines[-10:]).strip()
            log_fail_msg("Job returned non-zero exit code. "
                         "Last 10 lines:\n```\n{}\n```\n".format(msg))
            return False

        # Ensure all pass patterns were seen.
        if chk_passed:
            msg = ''.join(lines[-10:]).strip()
            log_fail_msg("One or more pass patterns not found:\n{}\n"
                         "Last 10 lines:\n```\n{}\n```\n".format(
                             pass_patterns, msg))
            return False

        return True

    def _link_odir(self, status):
        """Soft-links the job's directory based on job's status.

        The dispatched, passed and failed directories in the scratch area
        provide a quick way to get to the job that was executed.
        """

        dest = Path(self.deploy.sim_cfg.links[status], self.deploy.qual_name)

        # If dest exists, then atomically remove it and link the odir again.
        while True:
            try:
                os.symlink(self.deploy.odir, dest)
                break
            except FileExistsError:
                rm_path(dest)

        # Delete the symlink from dispatched directory if it exists.
        if status != "D":
            old = Path(self.deploy.sim_cfg.links['D'], self.deploy.qual_name)
            rm_path(old)
