# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import datetime
import logging as log
import os
import subprocess
from Launcher import ErrorMessage
from Launcher import Launcher
from Launcher import LauncherError
from utils import rm_path
from utils import VERBOSE


class NcLauncher(Launcher):
    """Implementation of Launcher to launch jobs using altair nc."""

    def __init__(self, deploy):
        """Initialize common class members."""

        super().__init__(deploy)

        # Popen object when launching the job.
        self.process = None

    def create_run_sh(self, full_path, cmd):
        run_file = os.path.join(full_path, 'run.sh')
        rm_path(run_file)
        lines = ['#!/bin/sh',
                 'function realpath {',
                 '  python -c "import os; print (os.path.realpath(\'$1\'))"',
                 '}',
                 'MY_FILEPATH=$(realpath "${BASH_SOURCE[0]}")',
                 'MY_DIR=$( dirname "${MY_FILEPATH}" )',
                 'cd $MY_DIR',
                 'export TMPDIR=$PWD/tmp',
                 'mkdir -p $TMPDIR',
                 'echo Launch start : `date`',
                 'SECONDS=0',
                 cmd,
                 'echo Launch end : `date`',
                 'echo CPU time : $SECONDS sec']
        with open(run_file, 'w') as f:
            f.write('\n'.join(lines))
        os.chmod(run_file, 0o755)

    def get_submit_cmd(self, interactive_flags):
        exetool = self.deploy.sim_cfg.tool
        log_file = self.deploy.get_log_path()
        job_name = self.deploy.full_name
        cmd = self.deploy.cmd
        odir = self.deploy.odir

        # TODO: These tool-specific names need moving into an hjson config
        # file.
        if (exetool == 'xcelium'):
            license_args = ['-r', 'License:Xcelium_Single_Core/1']
        elif (exetool == 'vcs'):
            license_args = ['-r', 'License:VCSRuntime_Net/1']
        else:
            license_args = []
        license_args.extend(['-r', 'RAM/8192', '-r', 'CORES/2'])

        self.create_run_sh(odir, cmd)

        return (['nc', 'run', '-D',
                 '-e', 'SNAPSHOT',
                 '-nodb', '-forcelog',
                 '-l', log_file,
                 '-set', job_name] +
                license_args +
                interactive_flags +
                ['--', f'{odir}/run.sh'])

    def _do_launch(self):
        # Compute the environment for the subprocess by overriding environment
        # variables of this process with matching ones from self.deploy.exports
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

        if self.deploy.sim_cfg.interactive:
            # Interactive: Set RUN_INTERACTIVE to 1
            exports['RUN_INTERACTIVE'] = '1'
            interactive_flags = ['-I']
            cmd_arr = self.get_submit_cmd(interactive_flags)
            log.log(VERBOSE, '[Executing]:\n{}\n\n'.format(self.deploy.cmd))
            self.process = subprocess.Popen(cmd_arr,
                                            stdin=None,
                                            stdout=None,
                                            stderr=subprocess.STDOUT,
                                            # string mode
                                            universal_newlines=True,
                                            env=exports,
                                            cwd=self.deploy.odir)

            # Wait until the process exits
            self.process.wait()
        else:
            try:
                interactive_flags = ['-nolog', '-wl']
                cmd_arr = self.get_submit_cmd(interactive_flags)
                # Using file open instead of with open as
                # it is being using in the subprocess.Popen call
                # which returns immediately after launching the cmd
                # and we want the file to remain open throughout the process
                f = open(self.deploy.get_log_path(),
                         'w',
                         encoding='UTF-8',
                         errors='surrogateescape')
                f.write('[Executing]:\n{}\n\n'.format(self.deploy.cmd))
                f.flush()
                self.process = subprocess.Popen(cmd_arr,
                                                bufsize=4096,
                                                universal_newlines=True,
                                                stdout=f,
                                                stderr=f,
                                                env=exports,
                                                cwd=self.deploy.odir)
            except subprocess.SubprocessError as e:
                raise LauncherError(f'IO Error: {e}\n'
                                    f'See {self.deploy.get_log_path()}')
            finally:
                self._close_process()

        self._link_odir('D')

    def poll(self):
        """Check status of the running process.

        This returns 'D', 'P', 'F', or 'K'. If 'D', the job is still running.
        If 'P', the job finished successfully. If 'F', the job finished with
        an error. If 'K' it was killed.

        This function must only be called after running self.dispatch_cmd() and
        must not be called again once it has returned 'P' or 'F'.
        """

        assert self.process is not None
        elapsed_time = datetime.datetime.now() - self.start_time
        job_runtime_secs = elapsed_time.total_seconds()
        if self.process.poll() is None:
            timeout_mins = self.deploy.get_timeout_mins()
            if timeout_mins is not None and not self.deploy.gui:
                if job_runtime_secs > (timeout_mins * 60):
                    self._kill()
                    timeout_message = f'Job timed out after {timeout_mins} mins'
                    self._post_finish('K',
                                      ErrorMessage(line_number=None,
                                                   message=timeout_message,
                                                   context=[timeout_message]))
                    return 'K'
                else:
                    return 'D'
            else:
                return 'D'

        self.exit_code = self.process.returncode
        status, err_msg = self._check_status()
        self._post_finish(status, err_msg)
        return self.status

    def _kill(self):
        """Kill the running process.

        Try to kill the running process. Send SIGTERM
        and SIGKILL.
        """
        try:
            subprocess.run(['nc', 'stop', '-set', self.deploy.full_name,
                            '-sig', 'TERM,KILL'],
                           check=True,
                           stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE)
        except subprocess.CalledProcessError as e:
            log.error('Failed to kill job: {}'.format(
                e.stderr.decode('utf-8').strip()))

    def kill(self):
        """Kill the running process.

        This must be called between dispatching and reaping the process (the
        same window as poll()).

        """
        self._kill()
        self._post_finish(
            'K',
            ErrorMessage(line_number=None, message='Job killed!', context=[]))

    def _post_finish(self, status, err_msg):
        self._close_process()
        self.process = None
        super()._post_finish(status, err_msg)

    def _close_process(self):
        """Close the file descriptors associated with the process."""

        assert self.process
        if self.process.stdout:
            self.process.stdout.close()
