"""Copyright 2020 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
"""

import sys
import vsc
import csv
from tabulate import *  # NOQA
sys.path.append("pygen/")
from pygen_src.riscv_instr_pkg import *  # NOQA
from pygen_src.isa.riscv_cov_instr import riscv_cov_instr
from pygen_src.riscv_instr_cover_group import *  # NOQA
from pygen_src.isa.riscv_floating_point_instr import riscv_floating_point_instr


class riscv_instr_cov_test:
    """ Main class for applying the functional coverage test """

    def __init__(self):
        self.instr_cg = riscv_instr_cover_group()
        self.fd_ins = riscv_floating_point_instr()
        self.trace = {}
        self.csv_trace = []
        self.entry_cnt, self.total_entry_cnt, self.skipped_cnt, \
        self.unexpected_illegal_instr_cnt = 0, 0, 0, 0
        logging.basicConfig(filename='{}'.format(cfg.argv.log_file_name),
                            filemode='w',
                            format="%(filename)s %(lineno)s %(levelname)s %(message)s",
                            level=logging.DEBUG)

    def run_phase(self):
        self.csv_trace = cfg.argv.trace_csv.split(",")
        if not self.csv_trace:
            sys.exit("No CSV file found!")
        logging.info("{} CSV trace files to be "
                     "processed...\n".format(len(self.csv_trace)))

        expect_illegal_instr = False
        for csv_file in self.csv_trace:
            with open("{}".format(csv_file)) as trace_file:
                self.entry_cnt = 0
                header = []
                self.instr_cg.reset()
                csv_reader = csv.reader(trace_file, delimiter=',')
                line_count = 0
                # Get the header line
                for row in csv_reader:
                    if line_count == 0:
                        header = row
                        logging.info("Header: {}".format(header))
                    else:
                        entry = row
                        if len(entry) != len(header):
                            logging.info("Skipping malformed entry[{}]: "
                                         "[{}]".format(self.entry_cnt, entry))
                            self.skipped_cnt += 1
                        else:
                            self.trace["csv_entry"] = row
                            logging.info("-----------------------------"
                                         "-----------------------------")
                            for idx in range(len(header)):
                                if "illegal" in entry[idx]:
                                    expect_illegal_instr = True
                                self.trace[header[idx]] = entry[idx]
                                if header[idx] != "pad":
                                    logging.info("{} = {}".format(header[idx],
                                                                  entry[idx]))
                            self.post_process_trace()
                            if self.trace["instr"] in ["li", "ret", "la"]:
                                continue
                            if ("amo" in self.trace["instr"] or
                                    "lr" in self.trace["instr"] or
                                    "sc" in self.trace["instr"]):
                                # TODO: Enable functional coverage for AMO test
                                continue
                            if not self.sample():
                                if not expect_illegal_instr:
                                    logging.error("Found unexpected illegal "
                                                  "instr: {} "
                                                  "[{}]".format(self.trace[
                                                                    "instr"],
                                                                entry))
                                    self.unexpected_illegal_instr_cnt += 1
                        self.entry_cnt += 1
                    line_count += 1
                logging.info("[{}]: {} instr processed".format(csv_file,
                                                               self.entry_cnt))
                self.total_entry_cnt += self.entry_cnt
        logging.info("Finished processing {} trace CSV, {} "
                     "instructions".format(len(self.csv_trace),
                                           self.total_entry_cnt))
        if self.skipped_cnt > 0 or self.unexpected_illegal_instr_cnt > 0:
            logging.error("{} instruction skipped, {} illegal "
                          "instructions".format(self.skipped_cnt,
                                                self.unexpected_illegal_instr_cnt))
        self.get_coverage_report()

    def get_coverage_report(self):
        model = vsc.get_coverage_report_model()
        str_report = vsc.get_coverage_report(details=True)
        logging.info("Report:\n" + str_report)
        cov_dir = cfg.argv.log_file_name.split("/")[0]
        file = open('{}/CoverageReport.txt'.format(cov_dir), 'w')
        file.write("Groups Coverage Summary\n")
        file.write("Total groups in report: {}\n".format(
            len(model.covergroups)))
        headers = ["SCORE", "WEIGHT", "NAME"]
        table = []
        for cg in model.covergroups:
            table.append([cg.coverage, cg.weight, cg.name])
        file.write(tabulate(table, headers, tablefmt="grid",
                            numalign="center", stralign="center"))
        file.close()
        # If enabled, write in xml format to be read by pyucis-viewer (visualization)
        if cfg.argv.enable_visualization:
            vsc.write_coverage_db("{}/cov_db.xml".format(cov_dir))

    def post_process_trace(self):
        pass

    def sample(self):
        processed_instr_name = self.process_instr_name(self.trace["instr"])
        if processed_instr_name in riscv_instr_name_t.__members__:
            instr_name = riscv_instr_name_t[processed_instr_name]
            instruction = riscv_cov_instr()
            instruction.instr = instr_name
            # cov_instr is created, time to manually assign attributes
            # TODO: This will get fixed later when we get an inst from template
            instruction.assign_attributes()
            if (instruction.group.name in ["RV32I", "RV32M", "RV32C", "RV64I",
                                          "RV64M", "RV64C", "RV64F",
                                          "RV64D", "RV32B", "RV64B"]) \
                                      and (instruction.group in rcs.supported_isa):
                self.assign_trace_info_to_instr(instruction)
                instruction.pre_sample()
                self.instr_cg.sample(instruction)
            elif instruction.group.name in ["RV32D", "RV32F"] \
                 and instruction.group in rcs.supported_isa:
                self.assign_trace_info_to_instr(instruction)
                self.fd_ins.pre_sample(instruction)
                self.instr_cg.sample(instruction)
            return True
        logging.info("Cannot find opcode: {}".format(processed_instr_name))
        return False

    def assign_trace_info_to_instr(self, instruction):
        instruction.pc.set_val(get_val(self.trace["pc"], hexa=1))
        instruction.binary.set_val(get_val(self.trace["binary"], hexa=1))
        instruction.trace = self.trace["instr_str"]
        if instruction.instr.name in ["NOP", "WFI", "FENCE", "FENCE_I",
                                      "EBREAK", "C_EBREAK", "SFENCE_VMA",
                                      "ECALL", "C_NOP", "MRET", "SRET",
                                      "URET"]:
            return
        operands = self.trace["operand"].split(",")
        if instruction.group.name in ["RV32D", "RV32F"]:
            self.fd_ins.update_src_regs(instruction, operands)
        else:
            instruction.update_src_regs(operands)

        gpr_update = self.trace["gpr"].split(";")
        if len(gpr_update) == 1 and gpr_update[0] == "":
            gpr_update = []
        for dest in gpr_update:
            pair = dest.split(":")
            if len(pair) != 2:
                logging.error("Illegal gpr update format: {}".format(dest))
            if instruction.group.name in ["RV32D", "RV32F"]:
                self.fd_ins.update_dst_regs(instruction, pair[0], pair[1])
            else:
                instruction.update_dst_regs(pair[0], pair[1])

    def process_instr_name(self, instruction):
        instruction = instruction.upper()
        instruction = instruction.replace(".", "_")
        instruction = self.update_instr_name(instruction)
        return instruction

    @staticmethod
    def update_instr_name(instruction):
        switcher = {
            # Rename to new name as ovpsim still uses old name
            "FMV_S_X": "FMV_W_X",
            "FMV_X_S": "FMV_X_W",
            # Convert pseudoinstructions
            "FMV_S": "FSGNJ_S",
            "FABS_S": "FSGNJX_S",
            "FNEG_S": "FSGNJN_S",
            "FMV_D": "FSGNJ_D",
            "FABS_D": "FSGNJX_D",
            "FNEG_D": "FSGNJN_D",
        }
        # if instruction is not present in the dictionary,second argument well
        # be assigned as default value of passed argument
        instruction = switcher.get(instruction, instruction)
        return instruction


cov_test = riscv_instr_cov_test()
cov_test.run_phase()
