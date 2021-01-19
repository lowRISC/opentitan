# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import locale
import logging
import os
import re
import shlex
import signal
import subprocess
import time
from pathlib import Path

import serial

log = logging.getLogger(__name__)


class Process:
    def __init__(self,
                 cmd,
                 logdir,
                 cwd=None,
                 startup_done_expect=None,
                 startup_timeout=None,
                 default_filter_func=None):
        """Utility class used to spawn an interact with processes.

        Args:
            cmd: Command line argument used to spawn process.
            logdir: Directory used to store STDOUT and STDERR output.
            cwd: Working directory used to spawn process.
            startup_done_expect: Pattern used to check at process startup time.
            startup_timeout: Timeout in seconds for |startup_done_expect| check.
            default_filter_func: Default function to filter all stdout/stderr
                output with when matching it with find_in_output().
        """
        if isinstance(cmd, str):
            self.cmd = shlex.split(cmd)
        else:
            self.cmd = [str(c) for c in cmd]
        self.logdir = str(logdir)
        self.cwd = str(cwd)
        self.startup_done_expect = startup_done_expect
        self.startup_timeout = startup_timeout
        self.proc = None
        self.logger = logging.getLogger(__name__)

        self._f_stdout = None
        self._f_stderr = None
        self._f_stdout_r = None
        self._f_stderr_r = None

        self.default_filter_func = default_filter_func

    def __del__(self):
        try:
            self.proc.kill()
            self._f_stdout.close()
            self._f_stderr.close()
            self._f_stdout_r.close()
            self._f_stderr_r.close()
        except Exception:
            pass

    def is_running(self):
        """ Check if the process is running

        Returns:
           True if the process is running, False otherwise
        """
        return self.proc and self.proc.poll() is not None

    def run(self):
        """Start process with command line configured in constructor."""
        cmd_name = os.path.basename(self.cmd[0])

        # Enforce line-buffered STDOUT even when sending STDOUT/STDERR to file.
        # If applications don't fflush() STDOUT manually, STDOUT goes through
        # a 4kB buffer before we see any output, which prevents searching for
        # the string indicating a successful startup.
        # see discussion at http://www.pixelbeat.org/programming/stdio_buffering/
        cmd = ['stdbuf', '-oL'] + self.cmd
        self.logger.info("Running command " + ' '.join(cmd))

        logfile_stdout = os.path.join(self.logdir,
                                      "{}.stdout".format(cmd_name))
        logfile_stderr = os.path.join(self.logdir,
                                      "{}.stderr".format(cmd_name))
        self.logger.debug("Capturing STDOUT at " + logfile_stdout)
        self.logger.debug("Capturing STDERR at " + logfile_stderr)

        self._f_stdout = open(logfile_stdout, 'w')
        self._f_stderr = open(logfile_stderr, 'w')
        self.proc = subprocess.Popen(cmd,
                                     cwd=self.cwd,
                                     universal_newlines=True,
                                     bufsize=1,  # Use line buffering
                                     stdin=subprocess.PIPE,
                                     stdout=self._f_stdout,
                                     stderr=self._f_stderr)

        self._f_stdout_r = open(logfile_stdout, 'r')
        self._f_stderr_r = open(logfile_stderr, 'r')

        # no startup match pattern given => startup done!
        if self.startup_done_expect is None:
            return True

        # check if the string indicating a successful startup appears in the
        # the program output (STDOUT or STDERR).
        try:
            init_done = self.find_in_output(pattern=self.startup_done_expect,
                                            timeout=self.startup_timeout)
            if init_done is None:
                raise RuntimeError('No match for pattern {!r} in startup.'
                                   .format(str(self.startup_done_expect)))
        except subprocess.TimeoutExpired as err:
            # On time-out, find_in_output will raise a TimeoutExpired exception
            # but (of course) it doesn't know the command it's running, so we
            # amend it as it goes past.
            assert err.cmd is None
            err.cmd = cmd
            raise

        self.logger.info("Startup sequence matched, startup done.")

        return True

    def terminate(self):
        """Terminates process started by run call."""
        if self.proc is not None:
            self.proc.terminate()

    def send_ctrl_c(self):
        """Sends SIGINT to process started by run call."""
        if self.proc is not None:
            self.proc.send_signal(signal.SIGINT)

    def expect(self, stdin_data=None, pattern=None, timeout=None):
        """Write data to STDIN and check if the output is as expected.

        Args:
            stdin_data: Data to send to STDIN.
            pattern: Pattern to search for after sending |stdin_data|.
            timeout: Timeout in seconds for |pattern| check.
        Returns:
            True if |pattern| found, False otherwise.
        """
        # We don't get STDOUT/STDERR from subprocess.communicate() as it's
        # redirected to file. We need to read the files instead.

        # XXX: races (false positives) can happen here if output is generated
        # before the input is sent to the process.
        if pattern is None:
            self._f_stdout_r.seek(0, 2)

        self.proc.stdin.write(stdin_data)
        self.proc.stdin.flush()

        if pattern is None:
            return True

        return self.find_in_output(pattern, timeout) is not None

    def find_in_output(self,
                       pattern,
                       timeout,
                       from_start=False,
                       filter_func=None):
        """Read STDOUT and STDERR to find an expected pattern.

        See find_in_files() for more documentation.
        """

        if filter_func is None:
            filter_func = self.default_filter_func

        def wait_func():
            """ Wait up to 0.2s until the process terminates.

            Returns:
                True if the subprocess terminated and a further wait will not
                produce more output, False otherwise.
            """
            try:
                self.proc.wait(timeout=0.2)
            except subprocess.TimeoutExpired:
                # The process did not yet terminate.
                return False

            # The process did terminate.
            return True

        return find_in_files([self._f_stdout_r, self._f_stderr_r],
                             pattern,
                             timeout,
                             filter_func=filter_func,
                             from_start=from_start,
                             wait_func=wait_func)


class LoggingSerial(serial.Serial):
    """ Acess to a serial console which logs all read/written data to file. """
    def __init__(self,
                 *args,
                 log_dir_path,
                 default_filter_func=None,
                 **kwargs):
        super().__init__(*args, **kwargs)

        self._log_to_device_fp = open(str(log_dir_path / 'to-device.log'),
                                      'wb')
        self._log_from_device_fp = open(str(log_dir_path / 'from-device.log'),
                                        'wb')

        self.default_filter_func = default_filter_func

        log.debug("Logging UART communication for {} to {}".format(
            self.port, str(log_dir_path)))

    def read(self, size=1):
        bytes = super().read(size)
        self._log_from_device_fp.write(bytes)

        # Explicitly flush the log file to ensure that data is present in the
        # log file when the conftest log dumping routines read the file after a
        # failed test.
        self._log_from_device_fp.flush()

        return bytes

    def write(self, data):
        retcode = super().write(data)
        self._log_to_device_fp.write(data)

        # Explicitly flush the log file to ensure that data is present in the
        # log file when the conftest log dumping routines read the file after a
        # failed test.
        self._log_to_device_fp.flush()

        return retcode

    def close(self):
        if self._log_to_device_fp:
            self._log_to_device_fp.close()

        if self._log_from_device_fp:
            self._log_from_device_fp.close()

        super().close()

    def log_add_marker(self, text: str):
        """ Write a marker text into the UART send and receive log files """
        text_b = text.encode('UTF-8')
        self._log_to_device_fp.write(text_b)
        self._log_from_device_fp.write(text_b)

    def drain_in(self, timeout=None, silence_time=.5):
        """ Read all available input data

        Args:
            timeout: Maximum time this function blocks, in seconds.
            silence_time: Consider the input drained if no new data can be read
                after this time, in seconds.
        Returns:
            The data read from the device.
        """
        t_end = None
        if timeout is not None:
            t_end = time.time() + timeout

        read_data = b''

        first_iteration = True
        while first_iteration or self.in_waiting != 0:
            if timeout is not None and time.time() >= t_end:
                break

            read_data += self.read(self.in_waiting)
            first_iteration = False
            time.sleep(silence_time)

        return read_data

    def find_in_output(self, pattern, timeout=None, filter_func=None):
        """ Expect a pattern to appear in one of the output lines.

        See the documentation of match_line() for a description of |pattern|.

        Args:
            pattern: Pattern to search for
            timeout: Timeout in seconds for |pattern| check.
            filter_func: Function to filter the output with before applying
                |pattern|. If none, the |self.default_filter_func| is used.
        Returns:
            None if |pattern| was not found, the return value of match_line()
            otherwise.
        """

        if filter_func is None:
            filter_func = self.default_filter_func

        t_end = None
        if timeout is not None:
            t_end = time.time() + timeout

        line = self.readline()
        while True:
            m = match_line(line, pattern, filter_func)
            if m is not None:
                return m

            if timeout is not None and time.time() >= t_end:
                break

            line = self.readline()

        return None


def dump_temp_files(tmp_path):
    """ Dump all files in a directory (typically logs) """
    logging.debug(
        "================= DUMP OF ALL TEMPORARY FILES =================")

    tmp_files = [
        Path(root) / f for root, dirs, files in os.walk(str(tmp_path))
        for f in files
    ]

    textchars = bytearray({7, 8, 9, 10, 12, 13, 27} |
                          set(range(0x20, 0x100)) - {0x7f})

    def is_binary_string(bytes):
        return bool(bytes.translate(None, textchars))

    for f in tmp_files:
        if f.name == '.lock':
            continue

        logging.debug("vvvvvvvvvvvvvvvvvvvv {} vvvvvvvvvvvvvvvvvvvv".format(f))

        if not f.is_file():
            logging.debug("[Not a regular file.]")
        elif f.stat().st_size > 50 * 1024:
            logging.debug("[File is too large to be shown ({} bytes).]".format(
                f.stat().st_size))
        else:
            with open(str(f), 'rb') as fp:
                data = fp.read(1024)
                if is_binary_string(data):
                    logging.debug(
                        "[File contains {} bytes of binary data.]".format(
                            f.stat().st_size))
                else:
                    fp.seek(0)
                    for line in fp:
                        line_str = line.decode(locale.getpreferredencoding(),
                                               errors='backslashreplace')
                        logging.debug(line_str.rstrip())
        logging.debug(
            "^^^^^^^^^^^^^^^^^^^^ {} ^^^^^^^^^^^^^^^^^^^^\n".format(f))


def load_sw_over_spi(tmp_path, spiflash_path, sw_test_bin, spiflash_args=[]):
    """ Use the spiflash utility to load software onto a device. """

    log.info("Flashing device software from {} over SPI".format(
        str(sw_test_bin)))

    cmd_flash = [spiflash_path, '--input', sw_test_bin] + spiflash_args
    p_flash = Process(cmd_flash, logdir=tmp_path, cwd=tmp_path)
    p_flash.run()
    p_flash.proc.wait(timeout=600)
    assert p_flash.proc.returncode == 0

    log.info("Device software flashed.")


def find_in_files(file_objects,
                  pattern,
                  timeout,
                  from_start=False,
                  filter_func=None,
                  wait_func=None):
    """Find a pattern in a list of file objects (file descriptors)

    See the documentation of match_line() for a description of |pattern|.

    Args:
        pattern: Pattern to search for
        timeout: Timeout in seconds for |pattern| check. Set to None to wait
            indefinitely.
        from_start: Search from the start of the given file objects.
        filter_func: Function to filter the output with before applying
            |pattern|. If none, the |default_filter_func| is used.
        wait_func: Function to call to wait. The function is expected to return
            True if no further output is expected in |file_objects| (this will
            end the wait loop before |timeout| expires), and False otherwise
            (more output could be produced).

    Returns:
        If |pattern| was found, returns the return value of match_line().
        Otherwise, returns None if |wait_func| returned True (signalling the
        end of the input with no match).

        Raises a subprocess.TimeoutExpired exception on timeout. This will have
        a |cmd| field of None.

    """

    t_end = None
    if timeout is not None:
        t_end = time.time() + timeout

    if wait_func is None:
        # By default, sleep for 200 ms when waiting for new input.
        def wait_func():
            time.sleep(.2)
            return False

    if from_start:
        for file_object in file_objects:
            file_object.seek(0)

    end_loop = False
    while True:
        for file_object in file_objects:
            for line in file_object:
                m = match_line(line.rstrip(), pattern, filter_func)
                if m is not None:
                    return m

        if end_loop:
            break

        if timeout is not None and time.time() >= t_end:
            raise subprocess.TimeoutExpired(None, timeout)

        # The wait function returns True to indicate that no more data will be
        # produced (e.g. because the producing process terminated). But we still
        # need to check one last time if the already produced data is matching
        # the `pattern`.
        end_loop = wait_func()

    return None


def match_line(line, pattern, filter_func=None):
    """
    Check if a line matches a pattern

    Line endings (CR/LR) are removed from |line| and neither matched nor
    returned.

    pattern can be of two types:
    1. A regular expression (any object with a match attribute, or a re.Pattern
       object in Python 3.7+). In this case, the pattern is matched against all
       lines and the result of re.match(pattern) (a re.Match object since
       Python 3.7) is returned.
    2. A string. In this case pattern is compared to each line with
       startswith(), and the full matching line is returned on a match.
    If no match is found None is returned.

    Optionally apply a filter to the line before matching it.
    """

    if isinstance(line, bytes):
        line = line.rstrip(b'\r\n')
    else:
        line = line.rstrip('\r\n')

    if filter_func is not None:
        line = filter_func(line)

    # TODO: Check for an instance of re.Pattern once we move to Python 3.7+
    if hasattr(pattern, "match"):
        return pattern.match(line)
    else:
        if line.startswith(pattern):
            return line

    return None


def filter_remove_device_sw_log_prefix(line):
    """
    Remove the file/line information in log messages produced by device software
    LOG() macros.
    """

    # See base_log_internal_core() in lib/base/log.c for the format description.
    pattern = r'^[IWEF?]\d{5} [a-zA-Z0-9\.-_]+:\d+\] '
    if isinstance(line, bytes):
        return re.sub(bytes(pattern, encoding='utf-8'), b'', line)
    else:
        return re.sub(pattern, '', line)


def filter_remove_sw_test_status_log_prefix(line):
    """
    Remove the logging prefix produced by the sw_test_status DV component.
    """

    # Example of a full prefix to be matched:
    # 1629002: (../src/lowrisc_dv_sw_test_status_0/sw_test_status_if.sv:42) [TOP.top_earlgrey_verilator.u_sw_test_status_if]
    pattern = r'\d+: \(.+/sw_test_status_if\.sv:\d+\) \[TOP\..+\] '
    if isinstance(line, bytes):
        return re.sub(bytes(pattern, encoding='utf-8'), b'', line)
    else:
        return re.sub(pattern, '', line)
