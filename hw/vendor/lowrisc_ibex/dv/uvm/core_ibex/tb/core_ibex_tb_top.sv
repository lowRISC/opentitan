// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module core_ibex_tb_top;

  import uvm_pkg::*;
  import core_ibex_test_pkg::*;

  wire clk;
  wire rst_n;
  logic fetch_enable;

  clk_if         ibex_clk_if(.clk(clk), .rst_n(rst_n));
  irq_if         irq_vif(.clk(clk));
  ibex_mem_intf  data_mem_vif(.clk(clk));
  ibex_mem_intf  instr_mem_vif(.clk(clk));


  // DUT probe interface
  core_ibex_dut_probe_if dut_if(.clk(clk));

  // RVFI interface
  core_ibex_rvfi_if rvfi_if(.clk(clk));

  // CSR access interface
  core_ibex_csr_if csr_if(.clk(clk));

  // You cannot override string parameters in VCS via the command line so a `define is used instead
  // that can be set from the command line. If no value has been specified this gives a default.
  `ifndef IBEX_MULTIPLIER_IMPLEMENTATION
    `define IBEX_MULTIPLIER_IMPLEMENTATION fast
  `endif

  parameter bit          PMPEnable       = 1'b0;
  parameter int unsigned PMPGranularity  = 0;
  parameter int unsigned PMPNumRegions   = 4;
  parameter bit RV32E                    = 1'b0;
  parameter bit RV32M                    = 1'b1;
  parameter bit RV32B                    = 1'b0;
  parameter bit BranchTargetALU          = 1'b0;
  parameter bit WritebackStage           = 1'b0;

  // VCS has issues taking a string as a define, so we have to build up the string via the
  // pre-processor.
  parameter     MultiplierImplementation = `PRIM_STRINGIFY(`IBEX_CFG_MultiplierImplementation);

  ibex_core_tracing #(
    .DmHaltAddr               (`BOOT_ADDR + 'h0        ),
    .DmExceptionAddr          (`BOOT_ADDR + 'h4        ),
    .PMPEnable                (PMPEnable               ),
    .PMPGranularity           (PMPGranularity          ),
    .PMPNumRegions            (PMPNumRegions           ),
    .RV32E                    (RV32E                   ),
    .RV32M                    (RV32M                   ),
    .RV32B                    (RV32B                   ),
    .BranchTargetALU          (BranchTargetALU         ),
    .WritebackStage           (WritebackStage          ),
    .MultiplierImplementation (MultiplierImplementation)
  ) dut (
    .clk_i          (clk                  ),
    .rst_ni         (rst_n                ),
    .test_en_i      (1'b0                 ),
    .hart_id_i      (32'b0                ),
    .boot_addr_i    (`BOOT_ADDR           ), // align with spike boot address
    .irq_software_i (irq_vif.irq_software ),
    .irq_timer_i    (irq_vif.irq_timer    ),
    .irq_external_i (irq_vif.irq_external ),
    .irq_fast_i     (irq_vif.irq_fast     ),
    .irq_nm_i       (irq_vif.irq_nm       ),
    .fetch_enable_i (dut_if.fetch_enable  ),
    .debug_req_i    (dut_if.debug_req     ),
    .data_req_o     (data_mem_vif.request ),
    .data_gnt_i     (data_mem_vif.grant   ),
    .data_rvalid_i  (data_mem_vif.rvalid  ),
    .data_addr_o    (data_mem_vif.addr    ),
    .data_we_o      (data_mem_vif.we      ),
    .data_be_o      (data_mem_vif.be      ),
    .data_rdata_i   (data_mem_vif.rdata   ),
    .data_wdata_o   (data_mem_vif.wdata   ),
    .data_err_i     (data_mem_vif.error   ),
    .instr_req_o    (instr_mem_vif.request),
    .instr_gnt_i    (instr_mem_vif.grant  ),
    .instr_rvalid_i (instr_mem_vif.rvalid ),
    .instr_addr_o   (instr_mem_vif.addr   ),
    .instr_rdata_i  (instr_mem_vif.rdata  ),
    .instr_err_i    (instr_mem_vif.error  ),
    .core_sleep_o   (dut_if.core_sleep    )
  );

  // Data load/store vif connection
  assign data_mem_vif.reset     = ~rst_n;
  // Instruction fetch vif connnection
  assign instr_mem_vif.reset    = ~rst_n;
  assign instr_mem_vif.we       = 0;
  assign instr_mem_vif.be       = 0;
  assign instr_mem_vif.wdata    = 0;
  // RVFI interface connections
  assign rvfi_if.valid          = dut.rvfi_valid;
  assign rvfi_if.order          = dut.rvfi_order;
  assign rvfi_if.insn           = dut.rvfi_insn;
  assign rvfi_if.trap           = dut.rvfi_trap;
  assign rvfi_if.intr           = dut.rvfi_intr;
  assign rvfi_if.mode           = dut.rvfi_mode;
  assign rvfi_if.ixl            = dut.rvfi_ixl;
  assign rvfi_if.rs1_addr       = dut.rvfi_rs1_addr;
  assign rvfi_if.rs2_addr       = dut.rvfi_rs2_addr;
  assign rvfi_if.rs1_rdata      = dut.rvfi_rs1_rdata;
  assign rvfi_if.rs2_rdata      = dut.rvfi_rs2_rdata;
  assign rvfi_if.rd_addr        = dut.rvfi_rd_addr;
  assign rvfi_if.rd_wdata       = dut.rvfi_rd_wdata;
  assign rvfi_if.pc_rdata       = dut.rvfi_pc_rdata;
  assign rvfi_if_pc_wdata       = dut.rvfi_pc_wdata;
  assign rvfi_if.mem_addr       = dut.rvfi_mem_addr;
  assign rvfi_if.mem_rmask      = dut.rvfi_mem_rmask;
  assign rvfi_if.mem_rdata      = dut.rvfi_mem_rdata;
  assign rvfi_if.mem_wdata      = dut.rvfi_mem_wdata;
  // Irq interface connections
  assign irq_vif.reset          = ~rst_n;
  // Dut_if interface connections
  assign dut_if.ecall           = dut.u_ibex_core.id_stage_i.controller_i.ecall_insn;
  assign dut_if.wfi             = dut.u_ibex_core.id_stage_i.controller_i.wfi_insn;
  assign dut_if.ebreak          = dut.u_ibex_core.id_stage_i.controller_i.ebrk_insn;
  assign dut_if.illegal_instr   = dut.u_ibex_core.id_stage_i.controller_i.illegal_insn_d;
  assign dut_if.dret            = dut.u_ibex_core.id_stage_i.controller_i.dret_insn;
  assign dut_if.mret            = dut.u_ibex_core.id_stage_i.controller_i.mret_insn;
  assign dut_if.reset           = ~rst_n;
  assign dut_if.priv_mode       = dut.u_ibex_core.priv_mode_id;
  // CSR interface connections
  assign csr_if.csr_access      = dut.u_ibex_core.csr_access;
  assign csr_if.csr_addr        = dut.u_ibex_core.csr_addr;
  assign csr_if.csr_wdata       = dut.u_ibex_core.csr_wdata;
  assign csr_if.csr_rdata       = dut.u_ibex_core.csr_rdata;
  assign csr_if.csr_op          = dut.u_ibex_core.csr_op;

  initial begin
    uvm_config_db#(virtual clk_if)::set(null, "*", "clk_if", ibex_clk_if);
    uvm_config_db#(virtual core_ibex_dut_probe_if)::set(null, "*", "dut_if", dut_if);
    uvm_config_db#(virtual core_ibex_csr_if)::set(null, "*", "csr_if", csr_if);
    uvm_config_db#(virtual core_ibex_rvfi_if)::set(null, "*", "rvfi_if", rvfi_if);
    uvm_config_db#(virtual ibex_mem_intf)::set(null, "*data_if_slave*", "vif", data_mem_vif);
    uvm_config_db#(virtual ibex_mem_intf)::set(null, "*instr_if_slave*", "vif", instr_mem_vif);
    uvm_config_db#(virtual irq_if)::set(null, "*", "vif", irq_vif);
    run_test();
  end

endmodule
