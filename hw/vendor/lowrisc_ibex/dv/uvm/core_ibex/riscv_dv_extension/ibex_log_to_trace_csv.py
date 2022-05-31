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
    from lib import RET_FATAL, gpr_to_abi, sint_to_hex, convert_pseudo_instr
    import logging

finally:
    sys.path = _OLD_SYS_PATH


INSTR_RE = \
    re.compile(r"^\s*(?P<time>\d+)\s+(?P<cycle>\d+)\s+(?P<pc>[0-9a-f]+)\s+"
               r"(?P<bin>[0-9a-f]+)\s+(?P<instr>\S+\s+\S+)\s*")
RD_RE = re.compile(r"(x(?P<rd>[1-9]\d*)=0x(?P<rd_val>[0-9a-f]+))")
ADDR_RE = re.compile(r"(?P<rd>[a-z0-9]+?),"
                     r"(?P<imm>[\-0-9]+?)"
                     r"\((?P<rs1>[a-z0-9]+)\)")


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
        if m is None:
            continue

        instr_cnt += 1
        # Write the extracted instruction to a csvcol buffer file
        trace_entry = RiscvInstructionTraceEntry()
        trace_entry.instr_str = m.group("instr")
        trace_entry.instr = m.group("instr").split()[0]
        trace_entry.pc = m.group("pc")
        trace_entry.binary = m.group("bin")
        if full_trace:
            expand_trace_entry(trace_entry, m.group("instr").split()[1])

        c = RD_RE.search(line)
        if c:
            abi_name = gpr_to_abi("x{}".format(c.group("rd")))
            gpr_entry = "{}:{}".format(abi_name, c.group("rd_val"))
            trace_entry.gpr.append(gpr_entry)

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


def expand_trace_entry(trace, operands):
    '''Expands a CSV trace entry for a single instruction.

    Operands are added to the CSV entry, converting from the raw
    register naming scheme (x0, x1, etc...) to ABI naming (a1, s1, etc...).

    '''
    operands = process_imm(trace.instr, trace.pc, operands)
    trace.instr, operands = \
        convert_pseudo_instr(trace.instr, operands, trace.binary)

    # process any instructions of the form:
    # <instr> <reg> <imm>(<reg>)
    n = ADDR_RE.search(operands)
    if n:
        trace.imm = get_imm_hex_val(n.group("imm"))
        operands = ','.join([n.group("rd"), n.group("rs1"), n.group("imm")])

    # Convert the operands into ABI format for the function coverage flow,
    # and store them into the CSV trace entry.
    trace.operand = convert_operands_to_abi(operands)


def process_imm(instr_name, pc, operands):
    """Process imm to follow RISC-V standard convention"""
    if instr_name not in ['beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu', 'c.beqz',
                          'c.bnez', 'beqz', 'bnez', 'bgez', 'bltz', 'blez',
                          'bgtz', 'c.j', 'j', 'c.jal', 'jal']:
        return operands

    idx = operands.rfind(',')
    if idx == -1:
        imm = operands
        return str(sint_to_hex(int(imm, 16) - int(pc, 16)))

    imm = operands[idx + 1:]
    imm = str(sint_to_hex(int(imm, 16) - int(pc, 16)))
    return operands[0:idx + 1] + imm


def check_ibex_uvm_log(uvm_log):
    """Process Ibex UVM simulation log.

    Process the UVM simulation log produced by the test to check for
    correctness, reports failure if an explicit error or failure is seen in the
    log or there's no explicit pass.

    Args:
      uvm_log:   the uvm simulation log

    Returns:
      A tuple of (passed, log_out).
      `passed` indicates whether the test passed or failed based on the
      log.
      `log_out` a list of relevant lines from the log that may indicate the
      source of the failure, if `passed` is true it will be empty.

    """
    passed = False
    failed = False

    log_out = []

    with open(uvm_log, "r") as log:
        # Simulation log has report summary at the end, which references
        # 'UVM_ERROR' which can cause false failures. The summary appears after
        # the test result so ignore any lines after the test result is seen for
        # 'UVM_ERROR' checking. If the loop terminated immediately when a test
        # result was seen it would miss issues where the test result is
        # (erronously) repeated multiple times with different results.
        test_result_seen = False

        for line in log:
            if ('UVM_ERROR' in line or 'UVM_FATAL' in line or 'Error' in line) \
                    and not test_result_seen:
                log_out.append(line.strip())
                failed = True

            if 'RISC-V UVM TEST PASSED' in line:
                test_result_seen = True
                passed = True

            if 'RISC-V UVM TEST FAILED' in line:
                test_result_seen = True
                failed = True
                break

    # If we saw PASSED and FAILED, that's a bit odd. But we should treat the
    # test as having failed.
    if failed:
        passed = False

    return (passed, log_out)


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
