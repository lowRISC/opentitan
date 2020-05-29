# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Convert ibex log to the standard trace CSV format

import argparse
import os
import re
import sys

_IBEX_ROOT = os.path.normpath(os.path.join(os.path.dirname(__file__),
                                           '../../../..'))
_DV_SCRIPTS = os.path.join(_IBEX_ROOT, 'vendor/google_riscv-dv/scripts')
_OLD_SYS_PATH = sys.path

# Import riscv_trace_csv and lib from _DV_SCRIPTS before putting sys.path back
# as it started.
try:
    sys.path.insert(0, _DV_SCRIPTS)

    from riscv_trace_csv import (RiscvInstructionTraceCsv,
                                 RiscvInstructionTraceEntry,
                                 get_imm_hex_val)
    from lib import RET_FATAL, gpr_to_abi, sint_to_hex
    import logging

finally:
    sys.path = _OLD_SYS_PATH


INSTR_RE = \
    re.compile(r"^\s*(?P<time>\d+)\s+(?P<cycle>\d+)\s+(?P<pc>[0-9a-f]+)\s+"
               r"(?P<bin>[0-9a-f]+)\s+(?P<instr>\S+\s+\S+)\s*")
RD_RE = re.compile(r"(x(?P<rd>[1-9]\d*)=0x(?P<rd_val>[0-9a-f]+))")
ADDR_RE = re.compile(r"(?P<imm>[\-0-9]+?)\((?P<rs1>.*)\)")


def _process_ibex_sim_log_fd(log_fd, csv_fd, full_trace=True):
    """Process ibex simulation log.

    Reads from log_fd, which should be a file object containing a trace from an
    Ibex simulation. Writes in a standard CSV format to csv_fd, which should be
    a file object opened for writing.

    If full_trace is true, this dumps information about operands for, replacing
    absolute branch destinations with offsets relative to the current pc.

    """
    instr_cnt = 0

    trace_csv = RiscvInstructionTraceCsv(csv_fd)
    trace_csv.start_new_trace()

    trace_entry = None

    for line in log_fd:
        if re.search("ecall", line):
            break

        # Extract instruction information
        m = INSTR_RE.search(line)
        if m:
            instr_cnt += 1
            # Write the extracted instruction to a csvcol buffer file
            trace_entry = RiscvInstructionTraceEntry()
            trace_entry.instr_str = m.group("instr")
            trace_entry.instr = m.group("instr").split()[0]
            trace_entry.pc = m.group("pc")
            trace_entry.binary = m.group("bin")
            if full_trace:
                # Convert the operands into ABI format for
                # the functional coverage flow
                operands = m.group("instr").split()[1]
                trace_entry.operand = convert_operands_to_abi(operands)
                process_trace(trace_entry)

        c = RD_RE.search(line)
        if c:
            trace_entry.gpr.append('{}:{}'
                                   .format(gpr_to_abi("x%0s" % c.group("rd")),
                                           c.group("rd_val")))
            trace_csv.write_trace_entry(trace_entry)

    return instr_cnt


def process_ibex_sim_log(ibex_log, csv, full_trace=1):
    """Process ibex simulation log.

    Extract instruction and affected register information from ibex simulation
    log and save to a standard CSV format.
    """
    logging.info("Processing ibex log : %s" % ibex_log)
    try:
        with open(ibex_log, "r") as log_fd, open(csv, "w") as csv_fd:
            count = _process_ibex_sim_log_fd(log_fd, csv_fd,
                                             True if full_trace else False)
    except FileNotFoundError:
        raise RuntimeError("Logfile %s not found" % ibex_log)

    logging.info("Processed instruction count : %d" % count)
    if not count:
        raise RuntimeError("No instructions in logfile: %s" % ibex_log)

    logging.info("CSV saved to : %s" % csv)


def convert_operands_to_abi(operand_str):
    """Convert the operand string to use ABI register naming.

    At this stage in the conversion of the Ibex log to CSV format, the operand
    string is in this format:
        "x6,x6,1000".
    This function converts the register names to their ABI equivalents as shown below:
        "t1,t1,1000".
    This step is needed for the RISCV-DV functional coverage step, as it assumes that
    all operand registers already follow the ABI naming scheme.

    Args:
        operand_str : A string of the operands for a given instruction

    Returns:
        A string of the operands for the instruction, with register names converted to ABI.
    """
    operand_list = operand_str.split(",")
    for i in range(len(operand_list)):
        converted_op = gpr_to_abi(operand_list[i])
        if converted_op != "na":
            operand_list[i] = converted_op
    return ",".join(operand_list)


def process_trace(trace):
    """ Process instruction trace """
    process_imm(trace)
    if trace.instr == 'jalr':
        n = ADDR_RE.search(trace.operand)
        if n:
            trace.imm = get_imm_hex_val(n.group("imm"))


def process_imm(trace):
    """Process imm to follow RISC-V standard convention"""
    if trace.instr in ['beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu', 'c.beqz',
                       'c.bnez', 'beqz', 'bnez', 'bgez', 'bltz', 'blez',
                       'bgtz', 'c.j', 'j', 'c.jal', 'jal']:
        idx = trace.operand.rfind(',')
        if idx == -1:
            imm = trace.operand
            imm = str(sint_to_hex(int(imm, 16) - int(trace.pc, 16)))
            trace.operand = imm
        else:
            imm = trace.operand[idx + 1:]
            imm = str(sint_to_hex(int(imm, 16) - int(trace.pc, 16)))
            trace.operand = trace.operand[0:idx + 1] + imm


def check_ibex_uvm_log(uvm_log, core_name, test_name, report, write=True):
    """Process Ibex UVM simulation log.

    This function will be used when a test disables the normal post_compare
    step. Process the UVM simulation log produced by the test to check for
    correctness

    Args:
      uvm_log:   the uvm simulation log
      core_name: the name of the core
      test_name: name of the test being checked
      report:    the output report file
      write:     enables writing to the log file. If equal to 'onfail',
                 write when the test fails. Otherwise (true, but not the
                 string 'onfail'), write unconditionally.

    Returns:
      A boolean indicating whether the test passed or failed based on the
      signature

    """
    passed = False
    failed = False

    with open(uvm_log, "r") as log:
        for line in log:
            if 'RISC-V UVM TEST PASSED' in line:
                passed = True

            if 'RISC-V UVM TEST FAILED' in line:
                failed = True
                break

    # If we saw PASSED and FAILED, that's a bit odd. But we should treat the
    # test as having failed.
    if failed:
        passed = False

    if write:
        fd = open(report, "a+") if report else sys.stdout

        fd.write("%s uvm log : %s\n" % (core_name, uvm_log))
        if passed:
            fd.write("%s : [PASSED]\n\n" % test_name)
        elif failed:
            fd.write("%s : [FAILED]\n\n" % test_name)

        if report:
            fd.close()

    return passed


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--log",
                        help="Input ibex simulation log (default: stdin)",
                        type=argparse.FileType('r'),
                        default=sys.stdin)
    parser.add_argument("--csv",
                        help="Output trace csv file (default: stdout)",
                        type=argparse.FileType('w'),
                        default=sys.stdout)
    parser.add_argument("--full_trace", type=int, default=1,
                        help="Enable full log trace")

    args = parser.parse_args()

    _process_ibex_sim_log_fd(args.log, args.csv,
                             True if args.full_trace else False)


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as err:
        sys.stderr.write('Error: {}\n'.format(err))
        sys.exit(RET_FATAL)
