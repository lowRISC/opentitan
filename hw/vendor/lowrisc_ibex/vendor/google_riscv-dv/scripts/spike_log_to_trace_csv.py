"""
Copyright 2019 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Convert spike sim log to standard riscv instruction trace format
"""

import argparse
import os
import re
import sys
import logging

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))

from riscv_trace_csv import *
from lib import *

RD_RE = re.compile(
    r"(core\s+\d+:\s+)?(?P<pri>\d)\s+0x(?P<addr>[a-f0-9]+?)\s+" \
    r"\((?P<bin>.*?)\)\s+(?P<reg>[xf]\s*\d*?)\s+0x(?P<val>[a-f0-9]+)" \
    r"(\s+(?P<csr>\S+)\s+0x(?P<csr_val>[a-f0-9]+))?")
CORE_RE = re.compile(
    r"core\s+\d+:\s+0x(?P<addr>[a-f0-9]+?)\s+\(0x(?P<bin>.*?)\)\s+(?P<instr>.*?)$")
ADDR_RE = re.compile(
    r"(?P<rd>[a-z0-9]+?),(?P<imm>[\-0-9]+?)\((?P<rs1>[a-z0-9]+)\)")
ILLE_RE = re.compile(r"trap_illegal_instruction")

LOGGER = logging.getLogger()


def process_instr(trace):
    if trace.instr == "jal":
        # Spike jal format jal rd, -0xf -> jal rd, -15
        idx = trace.operand.rfind(",")
        imm = trace.operand[idx + 1:]
        if imm[0] == "-":
            imm = "-" + str(int(imm[1:], 16))
        else:
            imm = str(int(imm, 16))
        trace.operand = trace.operand[0:idx + 1] + imm
    # Properly format operands of all instructions of the form:
    # <instr> <reg1> <imm>(<reg2>)
    # The operands should be converted into CSV as:
    # "<reg1>,<reg2>,<imm>"
    m = ADDR_RE.search(trace.operand)
    if m:
        trace.operand = "{},{},{}".format(
            m.group("rd"), m.group("rs1"), m.group("imm"))


def read_spike_instr(match, full_trace):
    """Unpack a regex match for CORE_RE to a RiscvInstructionTraceEntry

    If full_trace is true, extract operand data from the disassembled
    instruction.

    """

    # Extract the disassembled instruction.
    disasm = match.group('instr')

    # Spike's disassembler shows a relative jump as something like "j pc +
    # 0x123" or "j pc - 0x123". We just want the relative offset.
    disasm = disasm.replace('pc + ', '').replace('pc - ', '-')

    instr = RiscvInstructionTraceEntry()
    instr.pc = match.group('addr')
    instr.instr_str = disasm
    instr.binary = match.group('bin')

    if full_trace:
        opcode = disasm.split(' ')[0]
        operand = disasm[len(opcode):].replace(' ', '')
        instr.instr, instr.operand = \
            convert_pseudo_instr(opcode, operand, instr.binary)

        process_instr(instr)

    return instr


def read_spike_trace(path, full_trace):
    """Read a Spike simulation log at <path>, yielding executed instructions.

    This assumes that the log was generated with the -l and --log-commits options
    to Spike.

    If full_trace is true, extract operands from the disassembled instructions.

    Since Spike has a strange trampoline that always runs at the start, we skip
    instructions up to and including the one at PC 0x1010 (the end of the
    trampoline). At the end of a DV program, there's an ECALL instruction, which
    we take as a signal to stop checking, so we ditch everything that follows
    that instruction.

    This function yields instructions as it parses them as tuples of the form
    (entry, illegal). entry is a RiscvInstructionTraceEntry. illegal is a
    boolean, which is true if the instruction caused an illegal instruction trap.

    """

    # This loop is a simple FSM with states TRAMPOLINE, INSTR, EFFECT. The idea
    # is that we're in state TRAMPOLINE until we get to the end of Spike's
    # trampoline, then we switch between INSTR (where we expect to read an
    # instruction) and EFFECT (where we expect to read commit information).
    #
    # We yield a RiscvInstructionTraceEntry object each time we leave EFFECT
    # (going back to INSTR), we loop back from INSTR to itself, or we get to the
    # end of the file and have an instruction in hand.
    #
    # On entry to the loop body, we are in state TRAMPOLINE if in_trampoline is
    # true. Otherwise, we are in state EFFECT if instr is not None, otherwise we
    # are in state INSTR.

    end_trampoline_re = re.compile(r'core.*: 0x0*1010 ')

    in_trampoline = True
    instr = None

    with open(path, 'r') as handle:
        for line in handle:
            if in_trampoline:
                # The TRAMPOLINE state
                if end_trampoline_re.match(line):
                    in_trampoline = False
                continue

            if instr is None:
                # The INSTR state. We expect to see a line matching CORE_RE.
                # We'll discard any other lines.
                instr_match = CORE_RE.match(line)
                if not instr_match:
                    continue

                instr = read_spike_instr(instr_match, full_trace)

                # If instr.instr_str is 'ecall', we should stop.
                if instr.instr_str == 'ecall':
                    break

                continue

            # The EFFECT state. If the line matches CORE_RE, we should have been in
            # state INSTR, so we yield the instruction we had, read the new
            # instruction and continue. As above, if the new instruction is 'ecall',
            # we need to stop immediately.
            instr_match = CORE_RE.match(line)
            if instr_match:
                yield instr, False
                instr = read_spike_instr(instr_match, full_trace)
                if instr.instr_str == 'ecall':
                    break
                continue

            # The line doesn't match CORE_RE, so we are definitely on a follow-on
            # line in the log. First, check for illegal instructions
            if 'trap_illegal_instruction' in line:
                yield (instr, True)
                instr = None
                continue

            # The instruction seems to have been fine. Do we have commit data (from
            # the --log-commits Spike option)?
            commit_match = RD_RE.match(line)
            if commit_match:
                groups = commit_match.groupdict()
                instr.gpr.append(gpr_to_abi(groups["reg"].replace(' ', '')) +
                                 ":" + groups["val"])

                if groups["csr"] and groups["csr_val"]:
                    instr.csr.append(groups["csr"] + ":" + groups["csr_val"])

                instr.mode = commit_match.group('pri')

        # At EOF, we might have an instruction in hand. Yield it if so.
        if instr is not None:
            yield (instr, False)


def process_spike_sim_log(spike_log, csv, full_trace=0):
    """Process SPIKE simulation log.

    Extract instruction and affected register information from spike simulation
    log and write the results to a CSV file at csv. Returns the number of
    instructions written.

    """
    logging.info("Processing spike log : {}".format(spike_log))
    instrs_in = 0
    instrs_out = 0

    with open(csv, "w") as csv_fd:
        trace_csv = RiscvInstructionTraceCsv(csv_fd)
        trace_csv.start_new_trace()

        for (entry, illegal) in read_spike_trace(spike_log, full_trace):
            instrs_in += 1

            if illegal and full_trace:
                logging.debug("Illegal instruction: {}, opcode:{}"
                              .format(entry.instr_str, entry.binary))

            # Instructions that cause no architectural update (which includes illegal
            # instructions) are ignored if full_trace is false.
            #
            # We say that an instruction caused an architectural update if either we
            # saw a commit line (in which case, entry.gpr will contain a single
            # entry) or the instruction was 'wfi' or 'ecall'.
            if not (full_trace or entry.gpr or entry.instr_str in ['wfi',
                                                                   'ecall']):
                continue

            trace_csv.write_trace_entry(entry)
            instrs_out += 1

    logging.info("Processed instruction count : {}".format(instrs_in))
    logging.info("CSV saved to : {}".format(csv))
    return instrs_out


def main():
    # Parse input arguments
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=str, help="Input spike simulation log")
    parser.add_argument("--csv", type=str, help="Output trace csv_buf file")
    parser.add_argument("-f", "--full_trace", dest="full_trace",
                        action="store_true",
                        help="Generate the full trace")
    parser.add_argument("-v", "--verbose", dest="verbose", action="store_true",
                        help="Verbose logging")
    parser.set_defaults(full_trace=False)
    parser.set_defaults(verbose=False)
    args = parser.parse_args()
    setup_logging(args.verbose)
    # Process spike log
    process_spike_sim_log(args.log, args.csv, args.full_trace)


if __name__ == "__main__":
    main()
