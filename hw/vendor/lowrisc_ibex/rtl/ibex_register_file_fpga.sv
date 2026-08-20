// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * RISC-V Register File
 *
 * Register file with 31 or 15x 32 bit wide registers. Register 0 is fixed to 0.
 *
 * This register file is designed to make FPGA synthesis tools infer RAM primitives. For Xilinx
 * FPGA architectures, it will produce RAM32M primitives. Other vendors have not yet been tested.
 *
 * Three key parameters influence the number and size of physical registers:
 *
 * 1. RV32E == 1:
 *    Restricts the register file to 16 registers (x0–x15).
 *
 * 2. DummyInstructions == 1:
 *    Not implemented in this register file — the FPGA variant does not support dummy instructions.
 *
 * 3. BaseIsa == BaseIsaRV32IorCHERIoT:
 *    Allows dynamic switching between standard RV32I/E registers (configured by the parameters
 *    above) and CHERIoT register mode when `cheriot_enable_i == IbexMuBiOn`.
 *    In CHERIoT mode, the core operates on 16 registers (x0–x15). These registers are wider
 *    because they include `CapWidth` capability metadata in addition to standard data bits.
 *
 *    To save area, the upper physical registers (x16–x31) from non-CHERIoT mode are re-purposed
 *    as `rf_shared` storage to hold CHERIoT capability metadata. Therefore, `CapWidth` must be
 *    >= `DataWidth` so that in non-CHERIoT mode, standard data writes to upper registers can be
 *    zero-extended into `rf_shared`.
 */

 `include "prim_assert.sv"

module ibex_register_file_fpga import ibex_pkg::*; #(
  parameter base_isa_e            BaseIsa           = BaseIsaRV32I,
  parameter bit                   RV32E             = 0,
  parameter int unsigned          DataWidth         = 32,
  parameter bit                   DummyInstructions = 0,
  parameter logic [DataWidth-1:0] WordZeroVal       = '0,
  // Capability port width
  parameter int unsigned          CapWidth          = ibex_cheriot_pkg::REGCAP_W,
  parameter logic [CapWidth-1:0]  CapWordZeroVal    = '0
) (
  // Clock and Reset
  input  logic                 clk_i,
  input  logic                 rst_ni,

  input  logic                 test_en_i,
  input  logic                 dummy_instr_id_i,
  input  logic                 dummy_instr_wb_i,

  input  ibex_mubi_t           cheriot_enable_i,

  // Read port R1
  input  logic [4:0]           raddr_a_i,
  output logic [DataWidth-1:0] rdata_a_o,
  output logic [CapWidth-1:0]  rcap_a_o,

  // Read port R2
  input  logic [4:0]           raddr_b_i,
  output logic [DataWidth-1:0] rdata_b_o,
  output logic [CapWidth-1:0]  rcap_b_o,

  // Write port W1
  input  logic [4:0]           waddr_a_i,
  input  logic [DataWidth-1:0] wdata_a_i,
  input  logic [CapWidth-1:0]  wcap_a_i,
  input  logic                 we_a_i
);

  if (BaseIsa == BaseIsaRV32IorCHERIoT) begin : g_cheriot_rf

    // CapWidth must be larger than DataWidth to ensure no truncation in the non-CHERIoT mode
    `ASSERT_INIT(CapWidthGTEDataWidth, CapWidth >= DataWidth)

    // Decode CHERIoT enable (full 4-bit MuBi comparison against IbexMuBiOn).
    logic cheriot_enabled;
    assign cheriot_enabled = (cheriot_enable_i == IbexMuBiOn);

    // Physical registers
    logic [DataWidth-1:0] rf_data   [16]; // x0-x15 data (both modes)
    logic [CapWidth-1:0]  rf_shared [16]; // shared: cap (CHERIoT) or x16-x31 data (!CHERIoT,!RV32E)

    // DummyInstructions not supported in FPGA register file
    logic unused_dummy_instr;
    assign unused_dummy_instr = dummy_instr_id_i ^ dummy_instr_wb_i;

    // Note that the SystemVerilog LRM requires variables on the LHS of assignments within
    // "always_ff" to not be written to by any other process. However, to enable the initialization
    // of the inferred RAM primitives with non-zero values, below "initial" procedures are needed.
    // Therefore, we use "always" instead of the generally preferred "always_ff" for the synchronous
    // write procedures.

    // Data write: lower bank (waddr[4]=0), x1-x15 only (x0 is never written)
    always @(posedge clk_i) begin : sync_data_write
      if (we_a_i && !waddr_a_i[4] && (waddr_a_i[3:0] != '0)) begin
        rf_data[waddr_a_i[3:0]] <= wdata_a_i;
      end
    end : sync_data_write

    // Shared write:
    //   CHERIoT mode:     Capability write for x1-x15 (co-write with data, waddr[4]=0)
    //   non-CHERIoT mode: Data write for x16-x31 (waddr[4]=1, including x16 at index [0])
    always @(posedge clk_i) begin : sync_shared_write
      if (cheriot_enabled) begin
        if (we_a_i && !waddr_a_i[4] && (waddr_a_i[3:0] != '0)) begin
          rf_shared[waddr_a_i[3:0]] <= wcap_a_i;
        end
      end else if (!RV32E) begin
        if (we_a_i && waddr_a_i[4]) begin
          rf_shared[waddr_a_i[3:0]] <= CapWidth'(wdata_a_i);
        end
      end
    end : sync_shared_write

    // Make sure we initialize the RAM with the correct register reset values.
    initial begin
      for (int k = 0; k < 16; k++) begin
        rf_data[k]   = WordZeroVal;
        rf_shared[k] = CapWordZeroVal;
      end
    end

    // In CHERIoT mode all register addresses are 4-bit (implicit E extension). Hence, the MSB must
    // never be set. The bank-select bit is anyway forced to 0.
    `ASSERT(CheriotWaddrMSBClear,  cheriot_enabled |-> !waddr_a_i[4])
    `ASSERT(CheriotRaddrAMSBClear, cheriot_enabled |-> !raddr_a_i[4])
    `ASSERT(CheriotRaddrBMSBClear, cheriot_enabled |-> !raddr_b_i[4])

    // Data: raddr[4]=0 → rf_data (x0-x15)
    //       raddr[4]=1 → rf_shared lower DataWidth bits (x16-x31), non-CHERIoT only.
    // The bank-select is AND-gated with !cheriot_enabled so a spurious raddr[4]=1 in CHERIoT
    // mode reads from rf_data rather than returning capability bits as integer data.
    assign rdata_a_o = (raddr_a_i[4] && !cheriot_enabled) ?
      DataWidth'(rf_shared[raddr_a_i[3:0]]) : rf_data[raddr_a_i[3:0]];
    assign rdata_b_o = (raddr_b_i[4] && !cheriot_enabled) ?
      DataWidth'(rf_shared[raddr_b_i[3:0]]) : rf_data[raddr_b_i[3:0]];

    // Cap: gated to CapWordZeroVal in non-CHERIoT mode; x0 always returns CapWordZeroVal.
    assign rcap_a_o = cheriot_enabled ?
      ((raddr_a_i[3:0] == '0) ? CapWordZeroVal : rf_shared[raddr_a_i[3:0]]) : CapWordZeroVal;
    assign rcap_b_o = cheriot_enabled ?
      ((raddr_b_i[3:0] == '0) ? CapWordZeroVal : rf_shared[raddr_b_i[3:0]]) : CapWordZeroVal;

    // Reset not used in this register file version
    logic unused_rst_ni;
    assign unused_rst_ni = rst_ni;

    // Test enable signal not used in FPGA implementation
    logic unused_test_en;
    assign unused_test_en = test_en_i;

  end else begin : g_plain_rf

    // BaseIsaRV32I: original FPGA register file, no capability support
    localparam int ADDR_WIDTH = RV32E ? 4 : 5;
    localparam int NUM_WORDS  = 2 ** ADDR_WIDTH;

    logic [DataWidth-1:0] mem[NUM_WORDS];
    logic we; // write enable if writing to any register other than R0

    assign rdata_a_o = (raddr_a_i == '0) ? WordZeroVal : mem[raddr_a_i];
    assign rdata_b_o = (raddr_b_i == '0) ? WordZeroVal : mem[raddr_b_i];

    // we select
    assign we = (waddr_a_i == '0) ? 1'b0 : we_a_i;

    // Note that the SystemVerilog LRM requires variables on the LHS of assignments within
    // "always_ff" to not be written to by any other process. However, to enable the initialization
    // of the inferred RAM32M primitives with non-zero values, below "initial" procedure is needed.
    // Therefore, we use "always" instead of the generally preferred "always_ff" for the synchronous
    // write procedure.
    always @(posedge clk_i) begin : sync_write
      if (we == 1'b1) begin
        mem[waddr_a_i] <= wdata_a_i;
      end
    end : sync_write

    // Make sure we initialize the BRAM with the correct register reset value.
    initial begin
      for (int k = 0; k < NUM_WORDS; k++) begin
        mem[k] = WordZeroVal;
      end
    end

    // Reset not used in this register file version
    logic unused_rst_ni;
    assign unused_rst_ni = rst_ni;

    // Dummy instruction changes not relevant for FPGA implementation
    logic unused_dummy_instr;
    assign unused_dummy_instr = dummy_instr_id_i ^ dummy_instr_wb_i;

    // Test enable signal not used in FPGA implementation
    logic unused_test_en;
    assign unused_test_en = test_en_i;

    // No capability support
    assign rcap_a_o = CapWordZeroVal;
    assign rcap_b_o = CapWordZeroVal;

    logic unused_wcap_a;
    assign unused_wcap_a = ^wcap_a_i;

    logic unused_cheriot_enable;
    assign unused_cheriot_enable = ^cheriot_enable_i;

  end

endmodule
