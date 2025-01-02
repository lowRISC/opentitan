// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The following exclusions were manually added.

// The reason for the following five exclusions are that "d" in "assign wr_data = d;"
// is driven by "hw2reg.status.<alert_name>.d = 1'b1' inside the "sram_ctrl" module.
CHECKSUM: "2099741489 2073313596"
INSTANCE: tb.dut.u_reg_regs.u_status_bus_integ_error.wr_en_data_arb
ANNOTATION: "[UNR] all inputs are constant"
Block 2 "1620753216" "assign wr_data = d;"
INSTANCE: tb.dut.u_reg_regs.u_status_init_error.wr_en_data_arb
ANNOTATION: "[UNR] all inputs are constant"
Block 2 "1620753216" "assign wr_data = d;"
CHECKSUM: "2099741489 2073313596"
INSTANCE: tb.dut.u_reg_regs.u_status_escalated.wr_en_data_arb
ANNOTATION: "[UNR] all inputs are constant"
Block 2 "1620753216" "assign wr_data = d;"
CHECKSUM: "2099741489 2073313596"
INSTANCE: tb.dut.u_reg_regs.u_status_readback_error.wr_en_data_arb
ANNOTATION: "[UNR] all inputs are constant"
Block 2 "1620753216" "assign wr_data = d;"
CHECKSUM: "2099741489 2073313596"
INSTANCE: tb.dut.u_reg_regs.u_status_sram_alert.wr_en_data_arb
ANNOTATION: "[UNR] all inputs are constant"
Block 2 "1620753216" "assign wr_data = d;"
