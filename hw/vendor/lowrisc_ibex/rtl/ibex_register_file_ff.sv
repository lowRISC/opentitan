// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * RISC-V Register File
 *
 * Register file based on flip-flops. Register x0 is set to 0 (unless used for dummy instructions).
 * Use this register file when targeting FPGA synthesis or Verilator simulation.
 *
 * Three key parameters influence the number and size of physical registers:
 *
 * 1. RV32E == 1:
 *    Restricts the register file to 16 registers (x0–x15).
 *
 * 2. DummyInstructions == 1:
 *    Implements x0 as a physical register used to write the results of dummy instructions.
 *    It always reads back as zero for non-dummy instructions.
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
 *
 * These configuration options result in the following physical register allocations:
 * +---------+-------+-------+--------------------+--------------------+-----------------------+
 * | CHERIoT | Dummy | RV32E | rf_data Flops      | rf_shared Flops    | Total Storage (Flops) |
 * +---------+-------+-------+--------------------+--------------------+-----------------------+
 * |    1    |   1   |   0   | 16 x DataWidth     | 16 x CapWidth      | 16 x Data + 16 x Cap  |
 * |    1    |   1   |   1   | 16 x DataWidth     | 16 x CapWidth      | 16 x Data + 16 x Cap  |
 * |    1    |   0   |   0   | 15 x DataWidth     | 16 x CapWidth^     | 16 x Data^+ 15 x Cap^ |
 * |    1    |   0   |   1   | 15 x DataWidth     | 15 x CapWidth      | 15 x Data + 15 x Cap  |
 * |    0    |   1   |   0   | 32 x DataWidth     | N/A (plain array)  | 32 x Data             |
 * |    0    |   1   |   1   | 16 x DataWidth     | N/A (plain array)  | 16 x Data             |
 * |    0    |   0   |   0   | 31 x DataWidth     | N/A (plain array)  | 31 x Data             |
 * |    0    |   0   |   1   | 15 x DataWidth     | N/A (plain array)  | 15 x Data             |
 * +---------+-------+-------+--------------------+--------------------+-----------------------+
 * ^In this mode, the x16 register (part of the rf_shared flops) is only DataWidth wide since it's
 *  only used as a data register because it is the x0 register for the capability part in CHERIoT.
 */

`include "prim_assert.sv"

module ibex_register_file_ff import ibex_pkg::*; #(
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

    // Write decode: waddr[3:0] indexes within a 16-entry bank.
    // Bank select: waddr[4]=0 → rf_data and rf_shared cap (CHERIoT co-write);
    //              waddr[4]=1 → rf_shared upper data (non-CHERIoT).
    logic [15:0] we_a_dec;
    always_comb begin : we_a_decoder
      for (int unsigned i = 0; i < 16; i++) begin
        we_a_dec[i] = (waddr_a_i[3:0] == 4'(i)) ? we_a_i : 1'b0;
      end
    end

    // Write data for the shared bank: cap metadata in CHERIoT mode, zero-extended data otherwise.
    logic [CapWidth-1:0] wshared_data;
    assign wshared_data = cheriot_enabled ? wcap_a_i : CapWidth'(wdata_a_i);

    // Data flops for x1-x15 (lower bank, waddr[4]=0)
    for (genvar i = 1; i < 16; i++) begin : g_rf_data_flops
      logic [DataWidth-1:0] rf_reg_q;
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          rf_reg_q <= WordZeroVal;
        end else if (we_a_dec[i] && !waddr_a_i[4]) begin
          rf_reg_q <= wdata_a_i;
        end
      end
      assign rf_data[i] = rf_reg_q;
    end

    // Shared flops:
    //   CHERIoT mode:     Capability flops for x1-x15 (same enable as data write)
    //   non-CHERIoT mode: Data flops for x16-x31 (only if RV32E == 0)
    for (genvar i = 1; i < 16; i++) begin : g_rf_shared_flops
      logic [CapWidth-1:0] rf_reg_q;
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          rf_reg_q <= CapWordZeroVal;
        end else if ((cheriot_enabled && we_a_dec[i] && !waddr_a_i[4]) ||
                     (!cheriot_enabled && !RV32E && we_a_dec[i] && waddr_a_i[4])) begin
          rf_reg_q <= wshared_data;
        end
      end
      assign rf_shared[i] = rf_reg_q;
    end

    // Entry 0: rf_data[0] (x0 data) and rf_shared[0] (x0 cap in CHERIoT / x16 data in non-CHERIoT).
    logic [CapWidth-1:0] rcap_r0; // x0 cap read value (null or dummy-dependent)

    // With dummy instructions enabled, R0 behaves as a real register but will always return 0 for
    // real instructions.
    // Implement
    //   rf_data[0]   iff DummyInstruction defined (x0 dummy write data)
    //   rf_shared[0] if DummyInstruction since CHERIoT==1 here (x0 dummy write capability)
    //                if !RV32E (x16 register for RV32I)
    if (DummyInstructions) begin : g_dummy_r0
      // SEC_CM: CTRL_FLOW.UNPREDICTABLE
      logic we_data_r0;
      logic we_shared_r0;

      // Write enable for dummy R0 register (waddr_a_i will always be 0 for dummy instructions)
      assign we_data_r0   = we_a_dec[0] && !waddr_a_i[4] && dummy_instr_wb_i;
      assign we_shared_r0 = cheriot_enabled ? we_data_r0 :
                                              (!RV32E && we_a_dec[0] && waddr_a_i[4]);
      `ASSERT(DummyWriteTargetsX0, we_a_i && dummy_instr_wb_i |-> waddr_a_i == '0)

      logic [DataWidth-1:0] rf_data_r0_q;
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          rf_data_r0_q <= WordZeroVal;
        end else if (we_data_r0) begin
          rf_data_r0_q <= wdata_a_i;
        end
      end
      // Output the dummy data for dummy instructions, otherwise R0 reads as zero
      assign rf_data[0] = dummy_instr_id_i ? rf_data_r0_q : WordZeroVal;

      logic [CapWidth-1:0] rf_shared_r0_q;
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          rf_shared_r0_q <= CapWordZeroVal;
        end else if (we_shared_r0) begin
          rf_shared_r0_q <= wshared_data;
        end
      end
      // Output rf_shared[0] unconditionally for the x16 case
      // Output the dummy capability only for dummy instructions, otherwise R0 reads as zero
      assign rf_shared[0] = rf_shared_r0_q;
      assign rcap_r0 = dummy_instr_id_i ? rf_shared[0] : CapWordZeroVal;

    end else begin : g_normal_r0
      assign rf_data[0] = WordZeroVal;
      assign rcap_r0    = CapWordZeroVal;

      logic unused_dummy_instr;
      assign unused_dummy_instr = dummy_instr_id_i ^ dummy_instr_wb_i;

      // rf_shared[0] needs a real flop when x16 exists (!RV32E). Without dummy instructions, this
      // will never be used as a capability and only always for x16 data
      if (!RV32E) begin : g_rf_shared0_x16
        logic [DataWidth-1:0] rf_shared_r0_q;
        always_ff @(posedge clk_i or negedge rst_ni) begin
          if (!rst_ni) begin
            rf_shared_r0_q <= WordZeroVal;
          end else if (!cheriot_enabled && we_a_dec[0] && waddr_a_i[4]) begin
            rf_shared_r0_q <= wdata_a_i;
          end
        end
        assign rf_shared[0] = CapWidth'(rf_shared_r0_q);
      end else begin : g_rf_shared0_no_x16
        assign rf_shared[0] = CapWordZeroVal;

        logic unused_we_a_dec0;
        assign unused_we_a_dec0 = we_a_dec[0];
      end
    end

    // Read outputs

    // Data: raddr[4]=0 → rf_data (x0-x15)
    //       raddr[4]=1 → rf_shared lower DataWidth bits (x16-x31), non-CHERIoT only.
    // The bank-select is AND-gated with !cheriot_enabled so a spurious raddr[4]=1 in CHERIoT
    // mode reads from rf_data rather than returning capability bits as integer data.
    assign rdata_a_o = (raddr_a_i[4] && !cheriot_enabled) ?
    DataWidth'(rf_shared[raddr_a_i[3:0]]) : rf_data[raddr_a_i[3:0]];
    assign rdata_b_o = (raddr_b_i[4] && !cheriot_enabled) ?
    DataWidth'(rf_shared[raddr_b_i[3:0]]) : rf_data[raddr_b_i[3:0]];

    // Cap: gated to CapWordZeroVal in non-CHERIoT mode.
    assign rcap_a_o = cheriot_enabled ?
    ((raddr_a_i[3:0] == '0) ? rcap_r0 : rf_shared[raddr_a_i[3:0]]) : CapWordZeroVal;
    assign rcap_b_o = cheriot_enabled ?
    ((raddr_b_i[3:0] == '0) ? rcap_r0 : rf_shared[raddr_b_i[3:0]]) : CapWordZeroVal;

    logic unused_test_en;
    assign unused_test_en = test_en_i;

    // In CHERIoT mode all register addresses are 4-bit (implicit E extension). Hence, the MSB must
    // never be set. The bank-select bit is anyway forced to 0.
    `ASSERT(CheriotWaddrMSBClear,  cheriot_enabled |-> !waddr_a_i[4])
    `ASSERT(CheriotRaddrAMSBClear, cheriot_enabled |-> !raddr_a_i[4])
    `ASSERT(CheriotRaddrBMSBClear, cheriot_enabled |-> !raddr_b_i[4])

  end else begin : g_plain_rf

    // BaseIsaRV32I: original flip-flop register file, no capability support
    localparam int unsigned ADDR_WIDTH = RV32E ? 4 : 5;
    localparam int unsigned NUM_WORDS  = 2**ADDR_WIDTH;

    logic [DataWidth-1:0] rf_reg   [NUM_WORDS];
    logic [NUM_WORDS-1:0] we_a_dec;

    always_comb begin : we_a_decoder
      for (int unsigned i = 0; i < NUM_WORDS; i++) begin
        we_a_dec[i] = (waddr_a_i == 5'(i)) ? we_a_i : 1'b0;
      end
    end

    logic unused_strobe;
    assign unused_strobe = we_a_dec[0]; // this is never read from in this case

    // No flops for R0 as it's hard-wired to 0
    for (genvar i = 1; i < NUM_WORDS; i++) begin : g_rf_flops
      logic [DataWidth-1:0] rf_reg_q;

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          rf_reg_q <= WordZeroVal;
        end else if (we_a_dec[i]) begin
          rf_reg_q <= wdata_a_i;
        end
      end

      assign rf_reg[i] = rf_reg_q;
    end

    // With dummy instructions enabled, R0 behaves as a real register but will always return 0 for
    // real instructions.
    if (DummyInstructions) begin : g_dummy_r0
      // SEC_CM: CTRL_FLOW.UNPREDICTABLE
      logic                 we_r0_dummy;
      logic [DataWidth-1:0] rf_r0_q;

      // Write enable for dummy R0 register (waddr_a_i will always be 0 for dummy instructions)
      assign we_r0_dummy = we_a_i & dummy_instr_wb_i;
      `ASSERT(DummyWriteTargetsX0, we_a_i && dummy_instr_wb_i |-> waddr_a_i == '0)

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          rf_r0_q <= WordZeroVal;
        end else if (we_r0_dummy) begin
          rf_r0_q <= wdata_a_i;
        end
      end

      // Output the dummy data for dummy instructions, otherwise R0 reads as zero
      assign rf_reg[0] = dummy_instr_id_i ? rf_r0_q : WordZeroVal;

    end else begin : g_normal_r0
      logic unused_dummy_instr;
      assign unused_dummy_instr = dummy_instr_id_i ^ dummy_instr_wb_i;

      // R0 is nil
      assign rf_reg[0] = WordZeroVal;
    end

    assign rdata_a_o = rf_reg[raddr_a_i[ADDR_WIDTH-1:0]];
    assign rdata_b_o = rf_reg[raddr_b_i[ADDR_WIDTH-1:0]];

    // When RV32E=1 the address space is 4 bits wide; bit [4] of the read ports is unused.
    if (RV32E) begin : g_unused_raddr_msb
      logic [1:0] unused_raddr_msb;
      assign unused_raddr_msb = {raddr_a_i[4], raddr_b_i[4]};
    end

    // Signal not used in FF register file
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
