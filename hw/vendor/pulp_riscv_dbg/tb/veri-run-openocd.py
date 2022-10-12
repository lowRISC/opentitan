#!/usr/bin/python3
"""Launch riscv-dbg testbench and connect to openocd"""

import sys
from subprocess import Popen
from subprocess import PIPE, STDOUT
from os import getenv
import shlex

if __name__ == '__main__':
    veri_proc = Popen(shlex.split('make veri-run'),
                 stdin=PIPE, stdout=PIPE, stderr=STDOUT,
                 universal_newlines=True)
    for line in veri_proc.stdout:
        print(line, end='')
        if 'Listening on port' in line:
            print('Starting OpenOCD')
            break
        elif 'failed to bind socket' in line:
            print("Try 'killall testbench_verilator'", file=sys.stderr)
            exit(1)

    # try a few paths where openocd could be
    openocd = getenv('OPENOCD')
    if not openocd:
        openocd = getenv('RISCV')
        if openocd:
            openocd += '/bin/openocd'
    if not openocd:
        openocd = 'openocd'

    openocd_script = getenv('OPENOCD_SCRIPT')
    if not openocd_script:
        openocd_script = 'dm_compliance_test.cfg'

    print("Using '" + openocd)
    openocd_proc = Popen(shlex.split(openocd + ' -f ' + openocd_script),
                 stdin=PIPE, stdout=PIPE, stderr=STDOUT,
                 universal_newlines=True)
    print('Launched OpenOCD')

    ret = 1
    for line in openocd_proc.stdout:
        print(line, end='')
        if 'ALL TESTS PASSED' in line:
            ret = 0

    # Our spawned processes should have terminated by now. If not, we have to go after
    # them with the hammer (openocd likes to ignore sigterms when it gets stuck)
    if not openocd_proc.poll():
        openocd_proc.kill()

    if not veri_proc.poll():
        veri_proc.kill()

    exit(ret)
