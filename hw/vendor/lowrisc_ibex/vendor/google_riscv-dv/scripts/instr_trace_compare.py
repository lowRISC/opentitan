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

Compare the instruction trace CSV
"""

import argparse
import re
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))

from riscv_trace_csv import *


def compare_trace_csv(csv1, csv2, name1, name2, log,
                      in_order_mode=1,
                      coalescing_limit=0,
                      verbose=0,
                      mismatch_print_limit=5,
                      compare_final_value_only=0):
    """Compare two trace CSV file"""
    matched_cnt = 0
    mismatch_cnt = 0

    # ensure that in order mode is disabled if necessary
    if compare_final_value_only:
        in_order_mode = 0

    if log:
        fd = open(log, 'a+')
    else:
        fd = sys.stdout

    fd.write("{} : {}\n".format(name1, csv1))
    fd.write("{} : {}\n".format(name2, csv2))

    with open(csv1, "r") as fd1, open(csv2, "r") as fd2:
        instr_trace_1 = []
        instr_trace_2 = []
        trace_csv_1 = RiscvInstructionTraceCsv(fd1)
        trace_csv_2 = RiscvInstructionTraceCsv(fd2)
        trace_csv_1.read_trace(instr_trace_1)
        trace_csv_2.read_trace(instr_trace_2)
        trace_1_index = 0
        trace_2_index = 0
        mismatch_cnt = 0
        matched_cnt = 0
        if in_order_mode:
            gpr_val_1 = {}
            gpr_val_2 = {}
            for trace in instr_trace_1:
                trace_1_index += 1
                if len(trace.gpr) == 0:
                    continue
                # Check if there's a GPR change caused by this instruction
                gpr_state_change_1 = check_update_gpr(trace.gpr, gpr_val_1)
                if gpr_state_change_1 == 0:
                    continue
                # Move forward the other trace until a GPR update happens
                gpr_state_change_2 = 0
                while (gpr_state_change_2 == 0 and trace_2_index < len(
                        instr_trace_2)):
                    gpr_state_change_2 = check_update_gpr(
                        instr_trace_2[trace_2_index].gpr,
                        gpr_val_2)
                    trace_2_index += 1
                # Check if the GPR update is the same between trace 1 and 2
                if gpr_state_change_2 == 0:
                    mismatch_cnt += 1
                    fd.write("Mismatch[{}]:\n[{}] {} : {}\n".format(
                      mismatch_cnt, trace_1_index, name1,trace.get_trace_string()))
                    fd.write("{} instructions left in trace {}\n".format(
                      len(instr_trace_1) - trace_1_index + 1, name1))
                elif len(trace.gpr) != len(
                        instr_trace_2[trace_2_index - 1].gpr):
                    mismatch_cnt += 1
                    # print first few mismatches
                    if mismatch_cnt <= mismatch_print_limit:
                        fd.write("Mismatch[{}]:\n{}[{}] : {}\n".format(
                          mismatch_cnt, name1, trace_2_index - 1,
                          trace.get_trace_string()))
                        fd.write("{}[{}] : {}\n".format(
                          name2, trace_2_index - 1,
                          instr_trace_2[
                            trace_2_index - 1].get_trace_string()))
                else:
                    found_mismatch = 0
                    for i in range(len(trace.gpr)):
                        if trace.gpr[i] != instr_trace_2[trace_2_index - 1].gpr[i]:
                            mismatch_cnt += 1
                            found_mismatch = 1
                            # print first few mismatches
                            if mismatch_cnt <= mismatch_print_limit:
                                fd.write("Mismatch[{}]:\n{}[{}] : {}\n".format(
                                    mismatch_cnt, name1, trace_2_index - 1,
                                    trace.get_trace_string()))
                                fd.write("{}[{}] : {}\n".format(
                                    name2, trace_2_index - 1,
                                    instr_trace_2[
                                        trace_2_index - 1].get_trace_string()))
                            break
                    if not found_mismatch:
                        matched_cnt += 1
                # Break the loop if it reaches the end of trace 2
                if trace_2_index == len(instr_trace_2):
                    break
            # Check if there's remaining instruction that change architectural state
            if trace_2_index != len(instr_trace_2):
                while trace_2_index < len(instr_trace_2):
                    gpr_state_change_2 = check_update_gpr(
                        instr_trace_2[trace_2_index].gpr,
                        gpr_val_2)
                    if gpr_state_change_2 == 1:
                        fd.write("{} instructions left in trace {}\n".format(
                          len(instr_trace_2) - trace_2_index, name2))
                        mismatch_cnt += len(instr_trace_2) - trace_2_index
                        break
                    trace_2_index += 1
        else:
            pass
            # TODO: Enable out of order comparison
          #      # For processors which can commit multiple instructions in one cycle, the
          #      # ordering between different GPR update on that cycle could be
          #      # non-deterministic. If multiple instructions try to update the same GPR on
          #      # the same cycle, these updates could be coalesced to one update.
          #      gpr_trace_1 = {}
          #      gpr_trace_2 = {}
          #      parse_gpr_update_from_trace(instr_trace_1, gpr_trace_1)
          #      parse_gpr_update_from_trace(instr_trace_2, gpr_trace_2)
          #      if not compare_final_value_only:
          #        if len(gpr_trace_1) != len(gpr_trace_2):
          #          fd.write("Mismatch: affected GPR count mismtach %s:%d VS %s:%d\n" %
          #                   (name1, len(gpr_trace_1), name2, len(gpr_trace_2)))
          #          mismatch_cnt += 1
          #        for gpr in gpr_trace_1:
          #          coalesced_updates = 0
          #          if (len(gpr_trace_1[gpr]) != len(gpr_trace_2[gpr]) and
          #              coalescing_limit == 0):
          #            fd.write("Mismatch: GPR[%s] trace count mismtach %s:%d VS %s:%d\n" %
          #                     (gpr, name1, len(gpr_trace_1[gpr]),
          #                     name2, len(gpr_trace_2[gpr])))
          #            mismatch_cnt += 1
          #          trace_2_index = 0
          #          coalesced_updates = 0
          #          for trace_1_index in range(0, len(gpr_trace_1[gpr])-1):
          #            if (trace_2_index == len(gpr_trace_2[gpr])):
          #              break
          #            if int(gpr_trace_1[gpr][trace_1_index].rd_val, 16) != \
          #               int(gpr_trace_2[gpr][trace_2_index].rd_val, 16):
          #              if coalesced_updates >= coalescing_limit:
          #                coalesced_updates = 0
          #                mismatch_cnt += 1
          #                if mismatch_cnt <= mismatch_print_limit:
          #                  fd.write("Mismatch:\n")
          #                  fd.write("%s[%d] : %s\n" % (name1, trace_1_index,
          #                           gpr_trace_1[gpr][trace_1_index].get_trace_string()))
          #                  fd.write("%s[%d] : %s\n" % (name2, trace_2_index,
          #                           gpr_trace_2[gpr][trace_2_index].get_trace_string()))
          #                trace_2_index += 1
          #              else:
          #                if verbose:
          #                  fd.write("Skipping %s[%d] : %s\n" %
          #                           (name1, trace_1_index,
          #                           gpr_trace_1[gpr][trace_1_index].get_trace_string()))
          #                coalesced_updates += 1
          #            else:
          #              coalesced_updates = 0
          #              matched_cnt += 1
          #              if verbose:
          #                fd.write("Matched [%0d]: %s : %s\n" %
          #                         (trace_1_index, name1,
          #                         gpr_trace_1[gpr][trace_1_index].get_trace_string()))
          #              trace_2_index += 1
          #      # Check the final value match between the two traces
          #      for gpr in gpr_trace_1:
          #        if not compare_final_value_only:
          #          if (len(gpr_trace_1[gpr]) == 0 or len(gpr_trace_2[gpr]) == 0):
          #            mismatch_cnt += 1
          #            fd.write("Zero GPR[%s] updates observed: %s:%d, %s:%d\n" % (gpr,
          #                     name1, len(gpr_trace_1[gpr]), name2, len(gpr_trace_2[gpr])))
          #        else:
          #          if not gpr_trace_2.get(gpr):
          #            trace = RiscvInstructionTraceEntry()
          #            trace.rd_val = "0"
          #            trace.rd = gpr
          #            trace.instr_str = ""
          #            trace.binary = ""
          #            trace.addr = ""
          #            gpr_trace_2[gpr] = [trace]
          #        if int(gpr_trace_1[gpr][-1].rd_val, 16) != \
          #           int(gpr_trace_2[gpr][-1].rd_val, 16):
          #          mismatch_cnt += 1
          #          if mismatch_cnt <= mismatch_print_limit:
          #            fd.write("Mismatch final value:\n")
          #            fd.write("%s : %s\n" % (name1, gpr_trace_1[gpr][-1].get_trace_string()))
          #            fd.write("%s : %s\n" % (name2, gpr_trace_2[gpr][-1].get_trace_string()))
        if mismatch_cnt == 0:
            compare_result = "[PASSED]: {} matched\n".format(matched_cnt)
        else:
            compare_result = "[FAILED]: {} matched, {} mismatch\n".format(
                matched_cnt, mismatch_cnt)
        fd.write(compare_result + "\n")
        if log:
            fd.close()
        return compare_result


# def parse_gpr_update_from_trace(trace_csv, gpr_trace):
#  prev_val = {}
#  for trace in trace_csv:
#    if trace.rd != "":
#      if not (trace.rd in prev_val):
#        gpr_trace[trace.rd] = []
#        gpr_trace[trace.rd].append(trace)
#      elif prev_val[trace.rd] != trace.rd_val:
#        gpr_trace[trace.rd].append(trace)
#      prev_val[trace.rd] = trace.rd_val


def check_update_gpr(gpr_update, gpr):
    gpr_state_change = 0
    for update in gpr_update:
        if update == "":
            return 0
        item = update.split(":")
        if len(item) != 2:
            sys.exit("Illegal GPR update format:" + update)
        rd = item[0]
        rd_val = item[1]
        if rd in gpr:
            if rd_val != gpr[rd]:
                gpr_state_change = 1
        else:
            if int(rd_val, 16) != 0:
                gpr_state_change = 1
        gpr[rd] = rd_val
    return gpr_state_change


def main():
    # Parse input arguments
    parser = argparse.ArgumentParser()
    parser.add_argument("--csv_file_1", type=str,
                        help="Instruction trace 1 CSV")
    parser.add_argument("--csv_file_2", type=str,
                        help="Instruction trace 2 CSV")
    parser.add_argument("--csv_name_1", type=str,
                        help="Instruction trace 1 name")
    parser.add_argument("--csv_name_2", type=str,
                        help="Instruction trace 2 name")
    # optional arguments
    parser.add_argument("--log", type=str, default="",
                        help="Log file")
    parser.add_argument("--in_order_mode", type=int, default=1,
                        help="In order comparison mode")
    parser.add_argument("--gpr_update_coalescing_limit", type=int, default=1,
                        help="Allow the core to merge multiple updates to the \
                            same GPR into one. This option only applies to \
                            trace 2")
    parser.add_argument("--mismatch_print_limit", type=int, default=5,
                        help="Max number of mismatches printed")
    parser.add_argument("--verbose", type=int, default=0,
                        help="Verbose logging")
    parser.add_argument("--compare_final_value_only", type=int, default=0,
                        help="Only compare the final value of the GPR")

    args = parser.parse_args()

    # Compare trace CSV
    compare_trace_csv(args.csv_file_1, args.csv_file_2,
                      args.csv_name_1, args.csv_name_2, args.log,
                      args.in_order_mode, args.gpr_update_coalescing_limit,
                      args.verbose, args.mismatch_print_limit,
                      args.compare_final_value_only)


if __name__ == "__main__":
    main()
