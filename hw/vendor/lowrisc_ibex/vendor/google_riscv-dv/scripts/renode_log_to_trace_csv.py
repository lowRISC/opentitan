#!/usr/bin/env python3
"""
Converts Renode log to execution trace for RISC-V DV
"""

import argparse
import os
import re
import sys
import logging

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))

from riscv_trace_csv import *
from lib import *

# =============================================================================

GPR_NAMES = [
    ("x0",  "zero"),
    ("x1",  "ra"),
    ("x2",  "sp"),
    ("x3",  "gp"),
    ("x4",  "tp"),
    ("x5",  "t0"),
    ("x6",  "t1"),
    ("x7",  "t2"),
    ("x8",  "s0"),
    ("x9",  "s1"),
    ("x10", "a0"),
    ("x11", "a1"),
    ("x12", "a2"),
    ("x13", "a3"),
    ("x14", "a4"),
    ("x15", "a5"),
    ("x16", "a6"),
    ("x17", "a7"),
    ("x18", "s2"),
    ("x19", "s3"),
    ("x20", "s4"),
    ("x21", "s5"),
    ("x22", "s6"),
    ("x23", "s7"),
    ("x24", "s8"),
    ("x25", "s9"),
    ("x26", "s10"),
    ("x27", "s11"),
    ("x28", "t3"),
    ("x29", "t4"),
    ("x30", "t5"),
    ("x31", "t6"),
]

# =============================================================================


def process_renode_sim_log(log_name, csv_name):
    """
    Converts a Renode trace log to CSV format
    """

    # Build lookups
    gpr_to_name = {m[0]: m[1] for m in GPR_NAMES}
    known_gpr = {m[0].upper() for m in GPR_NAMES}

    # FIXME: We need a previous PC each time. Assume its value for the first
    # entry.
    prev_pc = "80000000"

    # FIXME: Assume initial state of all GPR set to 0
    state   = {m[0].upper(): "0" for m in GPR_NAMES}
    trace   = []

    with open(log_name, "r") as fp:
        for line in fp:

            line = line.strip()
            if not line:
                continue

            # Skip non-regdump
            if not line.startswith("REGDUMP:"):
                continue

            # Decode state
            fields = line.replace("REGDUMP:", "").split(",")
            regs = {fields[i]: fields[i+1] for i in range(0, len(fields), 2)}

            # Compute state difference
            diff  = {r: regs[r] for r in known_gpr \
                     if r in state and r in regs and state[r] != regs[r]}
            state = regs

            # Format the entry
            entry = RiscvInstructionTraceEntry()
            entry.pc        = prev_pc
            entry.binary    = "0"
            entry.operand   = ""
            entry.mode      = "0"

            # GPRs
            for x in range(32):
                name = "X{}".format(x)
                if name in diff:
                    lname = name.lower()
                    value = int(diff[name], 16)
                    entry.gpr.append("{}:{:08x}".format(gpr_to_name[lname], value))

            # CSRs
            # TODO:

            # Add only if there is a GPR/CSR change
            if entry.gpr or entry.csr:
                trace.append(entry)

            prev_pc = state["PC"]

    return trace


def write_csv(file_name, data):
    """
    Writes the trace to CSV
    """

    with open(file_name, "w") as fp:

        writer = RiscvInstructionTraceCsv(fp)
        writer.start_new_trace()

        for entry in data:
            writer.write_trace_entry(entry)

# ============================================================================


def main():
    # Parse input arguments
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=str, help="Input Renode simulation log")
    parser.add_argument("--csv", type=str, help="Output trace CSV file")
    parser.add_argument("-v", "--verbose", dest="verbose", action="store_true",
                        help="Verbose logging")
    parser.set_defaults(verbose=False)

    args = parser.parse_args()
    setup_logging(args.verbose)

    # Process Renode log
    trace = process_renode_sim_log(args.log, args.csv)
    # Write CSV
    write_csv(args.csv, trace)


if __name__ == "__main__":
    main()
