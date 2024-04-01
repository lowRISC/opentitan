// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

CHECKSUM: "3523621980"
ANNOTATION: "[UNR] all inputs are constant"
INSTANCE:tb.dut.u_seed_anchor.u_secure_anchor_buf.gen_generic.u_impl_generic

CHECKSUM: "1424864498"
ANNOTATION: "[UNR] all inputs are constant"
INSTANCE:tb.dut.u_tlul_adapter_sram.u_tlul_data_integ_enc_instr.u_data_gen

CHECKSUM: "1424864498"
ANNOTATION: "[UNR] all inputs are constant"
INSTANCE:tb.dut.u_tlul_adapter_sram.u_tlul_data_integ_enc_data.u_data_gen

CHECKSUM: "2503688253 3812101441"
INSTANCE: tb.dut.u_reg_regs.u_reg_if.u_rsp_intg_gen
ANNOTATION: "[UNR] all inputs are constant"
Block 1 "461445014" "assign rsp_intg = tl_i.d_user.rsp_intg;"
ANNOTATION: "[UNR] all inputs are constant"
Block 2 "2643129081" "assign data_intg = tl_i.d_user.data_intg;"

CHECKSUM: "281300783 1779845869"
INSTANCE: tb.dut.u_reg_regs.u_status_bus_integ_error.wr_en_data_arb
ANNOTATION: "[UNR] all inputs are constant"
Block 2 "1620753216" "assign wr_data = d;"
INSTANCE: tb.dut.u_reg_regs.u_status_init_error.wr_en_data_arb
ANNOTATION: "[UNR] all inputs are constant"
Block 2 "1620753216" "assign wr_data = d;"

CHECKSUM: "281300783 1779845869"
INSTANCE: tb.dut.u_reg_regs.u_status_escalated.wr_en_data_arb
ANNOTATION: "[UNR] all inputs are constant"
Block 2 "1620753216" "assign wr_data = d;"

CHECKSUM: "1296247128 1854270750"
INSTANCE: tb.dut
ANNOTATION: "[UNSUPPORTED] ACK can't come without REQ"
Condition 18 "153333633" "(key_ack & ((~key_req)) & ((~local_esc))) 1 -1" (2 "101")
ANNOTATION: "[LOWRISK] we don't issue a new init when there is a unfinished init"
Condition 11 "1796319142" "(init_done & ((~init_trig)) & ((~local_esc))) 1 -1" (2 "101")

CHECKSUM: "704952876 1147758610"
INSTANCE: tb.dut.u_prim_sync_reqack_data.u_prim_sync_reqack
ANNOTATION: "[UNSUPPORTED] ACK can't come without REQ"
Condition 1 "1414883863" "(src_req_i & src_ack_o) 1 -1" (1 "01")

CHECKSUM: "2574923469 2212102968"
INSTANCE: tb.dut.u_tlul_adapter_sram.u_sram_byte
ANNOTATION: "[UNR] this should not happen because the read latency of prim_ram_1p_scr is always 1 cycle"
Condition 2 "3441602297" "(gen_integ_handling.sram_d_ack && gen_integ_handling.rd_wait) 1 -1" (1 "01")

CHECKSUM: "835220981 1390693035"
INSTANCE: tb.dut.u_tlul_adapter_sram.u_rspfifo
ANNOTATION: "[UNR] when rspfifo is full, we don't expect to receive a request, as it's blocked at the req phase"
Condition 4 "786039886" "(wvalid_i & wready_o & ((~gen_normal_fifo.under_rst))) 1 -1" (2 "101")
ANNOTATION: "[LOWRISK] we don't issue a req when it's under reset"
Condition 7 "1709501387" "(((~gen_normal_fifo.empty)) & ((~gen_normal_fifo.under_rst))) 1 -1" (2 "10")

CHECKSUM: "835220981 869192578"
INSTANCE: tb.dut.u_tlul_adapter_sram.u_sramreqfifo
ANNOTATION: "[UNR] this fifo can never be full, because transactions can drain into u_rspfifo"
Condition 1 "644960181" "(gen_normal_fifo.full ? (2'(Depth)) : ((gen_normal_fifo.wptr_msb == gen_normal_fifo.rptr_msb) ? ((2'(gen_normal_fifo.wptr_value) - 2'(gen_normal_fifo.rptr_value))) : (((2'(Depth) - 2'(gen_normal_fifo.rptr_value)) + 2'(gen_normal_fifo.wptr_value))))) 1 -1" (2 "1")
ANNOTATION: "[UNR] this fifo can never be full, because transactions can drain into u_rspfifo"
Condition 5 "1324655787" "(rvalid_o & rready_i & ((~gen_normal_fifo.under_rst))) 1 -1" (2 "101")
ANNOTATION: "[UNR] this fifo can never be full, because transactions can drain into u_rspfifo"
Condition 8 "2721421913" "(gen_normal_fifo.fifo_wptr == (gen_normal_fifo.fifo_rptr ^ {1'b1, {(gen_normal_fifo.PTR_WIDTH - 1) {1'b0}}})) 1 -1" (2 "1")
ANNOTATION: "[UNR] this fifo can never be full, because transactions can drain into u_rspfifo"
Condition 6 "342355206" "(((~gen_normal_fifo.full)) & ((~gen_normal_fifo.under_rst))) 1 -1" (1 "01")

CHECKSUM: "2574923469 3226983296"
INSTANCE: tb.dut.u_tlul_adapter_sram.u_sram_byte
ANNOTATION: "[UNR] this should not happen because the read latency of prim_ram_1p_scr is always 1 cycle"
Branch 1 "4121297012" "gen_integ_handling.state_q" (4) "gen_integ_handling.state_q StWaitRd ,-,-,1,0,-"
ANNOTATION: "[UNR] this should not happen because prim_ram_1p_scr can always accept a read or write operation"
Branch 1 "4121297012" "gen_integ_handling.state_q" (7) "gen_integ_handling.state_q StWriteCmd ,-,-,-,-,0"

CHECKSUM: "835220981 2115631974"
INSTANCE: tb.dut.u_tlul_adapter_sram.u_sramreqfifo
ANNOTATION: "[UNR] this fifo can never be full, because transactions can drain into u_rspfifo"
Branch 0 "1862733684" "gen_normal_fifo.full" (0) "gen_normal_fifo.full 1,-"

CHECKSUM: "826810526 1029109911"
INSTANCE: tb.dut.u_tlul_lc_gate
ANNOTATION: "[LOWRISK] This happens in the 1st cycle after exiting reset. In order to cover it, need to drive TL items during reset, which isn't supported in the agent."
Condition 4 "4047466955" "(outstanding_txn == '0) 1 -1"
