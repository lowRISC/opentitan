# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import os
import shlex
import subprocess

from Launcher import ErrorMessage, Launcher, LauncherError


SLURM_QUEUE = os.environ.get("SLURM_QUEUE", "hw-m")
SLURM_MEM = os.environ.get("SLURM_MEM", "16G")
SLURM_MINCPUS = os.environ.get("SLURM_MINCPUS", "8")
SLURM_TIMEOUT = os.environ.get("SLURM_TIMEOUT", "240")
SLURM_CPUS_PER_TASK = os.environ.get("SLURM_CPUS_PER_TASK", "8")
SLURM_SETUP_CMD = os.environ.get("SLURM_SLURM_SETUP_CMD", "")


class SlurmLauncher(Launcher):
    # Misc common SlurmLauncher settings.
    max_odirs = 5

    def __init__(self, deploy):
        '''Initialize common class members.'''

        super().__init__(deploy)

        # Popen object when launching the job.
        self.process = None
        self.slurm_log_file = self.deploy.get_log_path() + '.slurm'

    def _do_launch(self):
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
            with open(self.slurm_log_file, 'w') as out_file:
                out_file.write("[Executing]:\n{}\n\n".format(self.deploy.cmd))
                out_file.flush()

                # Add a command delimiter if necessary
                slurm_setup_cmd = SLURM_SETUP_CMD
                if slurm_setup_cmd != '' and not slurm_setup_cmd.endswith(';'):
                    slurm_setup_cmd += ';'

                # Encapsulate the run command with the slurm invocation
                slurm_cmd = f'srun -p {SLURM_QUEUE} --mem={SLURM_MEM} --mincpus={SLURM_MINCPUS} ' \
                            f'--time={SLURM_TIMEOUT} --cpus-per-task={SLURM_CPUS_PER_TASK} ' \
                            f'bash -c "{slurm_setup_cmd} {self.deploy.cmd}"'

                log.info(f'Executing slurm command: {slurm_cmd}')
                self.process = subprocess.Popen(shlex.split(slurm_cmd),
                                                bufsize=4096,
                                                universal_newlines=True,
                                                stdout=out_file,
                                                stderr=out_file,
                                                env=exports)
        except subprocess.SubprocessError as e:
            raise LauncherError(f'IO Error: {e}\nSee {self.deploy.get_log_path()}')
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

        # Copy slurm job results to log file
        if os.path.exists(self.slurm_log_file):
            with open(self.slurm_log_file, 'r') as slurm_file:
                lines = slurm_file.readlines()
                with open(self.deploy.get_log_path(), 'a') as out_file:
                    for line in lines:
                        out_file.write(line)
                    out_file.flush()
            os.remove(self.slurm_log_file)

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
        self._post_finish(
            'K',
            ErrorMessage(line_number=None, message='Job killed!', context=[]))

    def _post_finish(self, status, err_msg):
        super()._post_finish(status, err_msg)
        self._close_process()
        self.process = None

    def _close_process(self):
        '''Close the file descriptors associated with the process.'''

        assert self.process
        if self.process.stdout:
            self.process.stdout.close()
