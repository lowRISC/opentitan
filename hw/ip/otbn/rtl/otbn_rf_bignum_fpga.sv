// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * ExtWLEN (312b) Wide Register File (WDRs)
 *
 * ExtWLEN allows bits to provide integrity checking to WLEN words on a 32-bit granule. Integrity
 * generation/checking implemented in wrapping otbn_rf_bignum module
 *
 * Features:
 * - 2 read ports
 * - 1 write port
 * - Half (WLEN) word write enables
 *
 * This register file is designed to make FPGA synthesis tools infer RAM primitives. For Xilinx
 * FPGA architectures, it will produce RAM32M primitives. Other vendors have not yet been tested.
 */
module otbn_rf_bignum_fpga
  import otbn_pkg::*;
#(
  parameter logic [BaseIntgWidth-1:0] WordZeroVal = '0
) (
  input  logic             clk_i,
  input  logic             rst_ni,

  input  logic [WdrAw-1:0]   wr_addr_i,
  input  logic [1:0]         wr_en_i,
  input  logic [ExtWLEN-1:0] wr_data_i,

  input  logic [WdrAw-1:0]   rd_addr_a_i,
  output logic [ExtWLEN-1:0] rd_data_a_o,

  input  logic [WdrAw-1:0]   rd_addr_b_i,
  output logic [ExtWLEN-1:0] rd_data_b_o,

  // Indicates whether a spurious WE has been seen in the last cycle.
  output logic               we_err_o
);


  // The reset is not used in this register file version.
  logic unused_rst_ni;
  assign unused_rst_ni = rst_ni;

  // This is only used for backdoor access in simulations.
  logic [ExtWLEN-1:0] rf [NWdr];
  logic [ExtWLEN-1:0] unused_rf [NWdr];
  assign unused_rf = rf;

  // Split registers into individual 39bit wide memories - otherwise the tool fails to properly
  // implement the non-zero memory intialization assignment in the initial block. Further, the
  // regfile is split into two sets of memories for clear separation of the enable terms.
  for (genvar i = 0; i < BaseWordsPerWLEN; i++) begin : gen_rf
    logic [BaseIntgWidth-1:0] rf_local [NWdr];
    // Sync write
    // Note that the SystemVerilog LRM requires variables on the LHS of assignments within
    // "always_ff" to not be written to by any other process. However, to enable the initialization
    // of the inferred RAM32M primitives with non-zero values, below "initial" procedure is needed.
    // Therefore, we use "always" instead of the generally preferred "always_ff" for the synchronous
    // write procedure.
    always @(posedge clk_i) begin
      if (wr_en_i[i/(BaseWordsPerWLEN/2)] == 1'b1) begin
        rf_local[wr_addr_i] <= wr_data_i[i*BaseIntgWidth+:BaseIntgWidth];
      end
    end

    // Make sure we initialize the BRAM with the correct register reset value.
    initial begin
      for (int k = 0; k < NWdr; k++) begin
        rf_local[k] = WordZeroVal;
      end
    end

    // Async read
    assign rd_data_a_o[i*BaseIntgWidth+:BaseIntgWidth] = rf_local[rd_addr_a_i];
    assign rd_data_b_o[i*BaseIntgWidth+:BaseIntgWidth] = rf_local[rd_addr_b_i];

    // SEC_CM: RF_BASE.DATA_REG_SW.GLITCH_DETECT
    // There is nothing to check here since the decoding happens inside the inferred
    // memory block.
    assign we_err_o = 1'b0;

  // This is only used for backdoor access in simulations.
`ifdef VERILATOR
  `define INC_BACKDOOR_LOAD
`elsif SIMULATION
  `define INC_BACKDOOR_LOAD
`endif
`ifdef INC_BACKDOOR_LOAD
    for (genvar k = 0; k < NWdr; k++) begin : gen_sim
      assign rf[k][i*BaseIntgWidth+:BaseIntgWidth] = rf_local[k];
    end
`undef INC_BACKDOOR_LOAD
`endif
  end

endmodule
