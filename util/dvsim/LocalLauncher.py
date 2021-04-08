# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import os
import shlex
import subprocess

from Launcher import ErrorMessage, Launcher, LauncherError


class LocalLauncher(Launcher):
    """
    Implementation of Launcher to launch jobs in the user's local workstation.
    """

    # Misc common LocalLauncher settings.
    max_odirs = 5

    def __init__(self, deploy):
        '''Initialize common class members.'''

        super().__init__(deploy)

        # Popen object when launching the job.
        self.process = None

    def _do_launch(self):
        # Update the shell's env vars with self.exports. Values in exports must
        # replace the values in the shell's env vars if the keys match.
        exports = os.environ.copy()
        if self.deploy.exports:
            exports.update(self.deploy.exports)

        # Clear the magic MAKEFLAGS variable from exports if necessary. This
        # variable is used by recursive Make calls to pass variables from one
        # level to the next. Here, self.cmd is a call to Make but it's
        # logically a top-level invocation: we don't want to pollute the flow's
        # Makefile with Make variables from any wrapper that called dvsim.
        if 'MAKEFLAGS' in exports:
            del exports['MAKEFLAGS']

        self._dump_env_vars(exports)

        try:
            f = open(self.deploy.get_log_path(),
                     "w",
                     encoding="UTF-8",
                     errors="surrogateescape")
            f.write("[Executing]:\n{}\n\n".format(self.deploy.cmd))
            f.flush()
            self.process = subprocess.Popen(shlex.split(self.deploy.cmd),
                                            bufsize=4096,
                                            universal_newlines=True,
                                            stdout=f,
                                            stderr=f,
                                            env=exports)
        except subprocess.SubprocessError as e:
            raise LauncherError('IO Error: {}\nSee {}'.format(
                e, self.deploy.get_log_path()))
        finally:
            self._close_process()

        self._link_odir("D")

    def poll(self):
        '''Check status of the running process

        This returns 'D', 'P' or 'F'. If 'D', the job is still running. If 'P',
        the job finished successfully. If 'F', the job finished with an error.

        This function must only be called after running self.dispatch_cmd() and
        must not be called again once it has returned 'P' or 'F'.
        '''

        assert self.process is not None
        if self.process.poll() is None:
            return 'D'

        self.exit_code = self.process.returncode
        status, err_msg = self._check_status()
        self._post_finish(status, err_msg)
        return status

    def kill(self):
        '''Kill the running process.

        This must be called between dispatching and reaping the process (the
        same window as poll()).

        '''
        assert self.process is not None

        # Try to kill the running process. Send SIGTERM first, wait a bit,
        # and then send SIGKILL if it didn't work.
        self.process.terminate()
        try:
            self.process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            self.process.kill()

        self._post_finish('K', ErrorMessage(line_number=None,
                                            message='Job killed!',
                                            context=[]))

    def _post_finish(self, status, err_msg):
        super()._post_finish(status, err_msg)
        self._close_process()
        self.process = None

    def _close_process(self):
        '''Close the file descriptors associated with the process.'''

        assert self.process
        if self.process.stdout:
            self.process.stdout.close()
