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

// As the depth of this FIFO is 1, the following conditions cannot be met.
CHECKSUM: "3215070453 33318353"
INSTANCE: tb.dut.u_tlul_adapter_sram.u_sram_byte.gen_integ_handling.u_sync_fifo.gen_normal_fifo.u_fifo_cnt
Condition 1 "2532211833" "(incr_wptr_i & (wptr_o == 1'((Depth - 1)))) 1 -1"
Condition 7 "687544961" "(full_o ? (1'(Depth)) : ((wptr_wrap_msb == rptr_wrap_msb) ? ((1'(wptr_o) - 1'(rptr_o))) : (((1'(Depth) - 1'(rptr_o)) + 1'(wptr_o))))) 1 -1"
Condition 3 "2597027294" "(incr_rptr_i & (rptr_o == 1'((Depth - 1)))) 1 -1"
CHECKSUM: "3215070453 1827096802"
INSTANCE: tb.dut.u_tlul_adapter_sram.u_sram_byte.gen_integ_handling.u_sync_fifo.gen_normal_fifo.u_fifo_cnt
Branch 0 "721764659" "full_o" (0) "full_o 1,-"
Branch 0 "721764659" "full_o" (2) "full_o 0,0"
Branch 0 "721764659" "full_o" (1) "full_o 0,1"
CHECKSUM: "3215070453 3446030929"
INSTANCE: tb.dut.u_tlul_adapter_sram.u_sram_byte.gen_integ_handling.u_sync_fifo.gen_normal_fifo.u_fifo_cnt
Block 19 "4019242409" "wptr_wrap_cnt_q <= (wptr_wrap_cnt_q + {{(WrapPtrW - 1) {1'b0}}, 1'b1});"
Block 28 "1113085816" "rptr_wrap_cnt_q <= (rptr_wrap_cnt_q + {{(WrapPtrW - 1) {1'b0}}, 1'b1});"
CHECKSUM: "3215070453 1827096802"
INSTANCE: tb.dut.u_tlul_adapter_sram.u_sram_byte.gen_integ_handling.u_sync_fifo.gen_normal_fifo.u_fifo_cnt
Branch 1 "2417346495" "(!rst_ni)" (3) "(!rst_ni) 0,0,0,1"
Branch 2 "456961687" "(!rst_ni)" (3) "(!rst_ni) 0,0,0,1"

// Exclude the default branch of the FSM inside the tlul_sram_byte module as we
// should not reach it under normal conditions.
CHECKSUM: "432309571 1160560609"
INSTANCE: tb.dut.u_tlul_adapter_sram.u_sram_byte
Branch 1 "2309313685" "gen_integ_handling.state_q" (46) "gen_integ_handling.state_q default,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-"
CHECKSUM: "432309571 1673264206"
INSTANCE: tb.dut.u_tlul_adapter_sram.u_sram_byte
Block 86 "2943004802" "alert_o = 1'b1;"
