// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module spi_host_data_stable_sva (
  input logic                                               rst_ni,
  input logic                                               cio_sck_o,
  input logic [spi_host_reg_pkg::NumCS-1:0]                 cio_csb_o,
  input logic [3:0]                                         cio_sd_i,
  input logic [3:0]                                         cio_sd_en_o,
  input spi_host_reg_pkg::spi_host_reg2hw_configopts_mreg_t configopts,
  input spi_device_pkg::passthrough_req_t                   passthrough_i
 );

  // Check to ensure cio_sd_o[i] stays stable for a whole clock cycle
  // Truth table:
  // ---------------------------------
  // CPHA | CPOL | posedge | negedge |
  // ---------------------------------
  // 0    | 0    | 1       | 0       | -> XNOR(cpha, cpol): drive negedge, sample posedge
  // 0    | 1    | 0       | 1       | -> XOR(cpha, cpol): drive posedge, sample negedge
  // 1    | 0    | 0       | 1       | -> XOR(cpha, cpol): drive posedge, sample negedge
  // 1    | 1    | 1       | 0       | -> XNOR(cpha, cpol): drive negedge, sample posedge
  // ---------------------------------


  // Driven in pos-edge, sampled in neg-edge
  reg    sampled_negedge_enable;
  // Driven in neg-edge, sampled in pos-edge
  reg    sampled_posedge_enable;
  logic  csbs;
  // Current design support NumCS=1 only
  assign csbs = &cio_csb_o;

  // HIGH when driven on pos-edge, sampled on the negedge
  assign sampled_negedge_enable = !csbs & (configopts.cpha.q ^ configopts.cpol.q);
  assign sampled_posedge_enable = !csbs & !sampled_negedge_enable;


  whole_cycle_data_stable_signal_checker #(.VECTOR_WIDTH(4))
  u_sva_cio_sd_i_whole_cycle_data_stable_check (
     .rst_ni (rst_ni),
     .sck_o (sck_o),
     .csb_o (csbs),
     .signal2check_i (cio_sd_i),
     .sampled_negedge_enable (sampled_negedge_enable),
     .sampled_posedge_enable (sampled_posedge_enable),
     .passthrough_en (passthrough_i.passthrough_en)
     );

  whole_cycle_data_stable_signal_checker #(.VECTOR_WIDTH(4))
  u_sva_cio_sd_en_o_whole_cycle_data_stable_check (
     .rst_ni (rst_ni),
     .sck_o (sck_o),
     .csb_o (csbs),
     .signal2check_i (cio_sd_en_o),
     .sampled_negedge_enable (sampled_negedge_enable),
     .sampled_posedge_enable (sampled_posedge_enable),
     .passthrough_en (passthrough_i.passthrough_en)
     );


endmodule // spi_host_data_stable_sva


module whole_cycle_data_stable_signal_checker #( parameter int VECTOR_WIDTH = 4 )
(
 input logic                    rst_ni,
 input logic                    sck_o,
 input logic                    csb_o,
 input logic [VECTOR_WIDTH-1:0] signal2check_i,
 input logic                    sampled_negedge_enable,
 input logic                    sampled_posedge_enable,
 input logic                    passthrough_en
 );

  import uvm_pkg::*;
`include "uvm_macros.svh"

  for (genvar i = 0; i < VECTOR_WIDTH; i++) begin : g_signal_stable_sva
    logic neg_value, pos_value;
    event check_posedge, check_negedge;

    always  @(negedge csb_o) begin
      // Initialising the neg/pos_value signals here, so they are ready for the first SPI cycle
      pos_value <= signal2check_i[i];
      neg_value <= signal2check_i[i];
      if (sampled_posedge_enable) begin
        @(negedge sck_o);
        pos_value <= signal2check_i[i];
      end
      if (sampled_negedge_enable) begin
        @(posedge sck_o);
        neg_value <= signal2check_i[i];
      end
    end // always  @ (negedge csb_o)


  always @(negedge sck_o or negedge rst_ni) begin
    if (!rst_ni) begin
      neg_value <= 0;
    end else if (!csb_o) begin
      neg_value <= signal2check_i[i];
      if (sampled_negedge_enable) begin
        // TODO: remove IF below when passthrough mode is handled thorougly
        // SPI-host block level TB drives gibberish to test passthru, which
        // causes the assertion to fire. Until passthrough is tested via driving
        // sensible SPI data is best to disable this SVA
        if (!passthrough_en)
          -> check_negedge;
      end
    end
  end

  always @(posedge sck_o or negedge rst_ni) begin
    if (!rst_ni) begin
      pos_value <= 0;
    end else if (!csb_o) begin
      pos_value <= signal2check_i[i];
      if (sampled_posedge_enable) begin
        // TODO: remove IF below when passthrough mode is handled thorougly
        // SPI-host block level TB drives gibberish to test passthru, which
        // causes the assertion to fire. Until passthrough is tested via driving
        // sensible SPI data is best to disable this SVA
        if (!passthrough_en)
          -> check_posedge;
      end
    end
  end // always @ (posedge sck_o or negedge rst_ni)

  NEGEDGE_SAME_VALUE_CHECK_P: assert property (@(check_negedge) pos_value == neg_value) begin
    `uvm_info("NEGEDGE_SAME_VALUE_CHECK_P", $sformatf("%m: [i=%0d] - ASSERTION PASSED %t",i, $time),
              UVM_DEBUG);
  end
  else begin
    `uvm_error("NEGEDGE_SAME_VALUE_CHECK_P", {$sformatf("%m: [i=%0d] - ASSERTION FAILED",i),
                                              $sformatf(" pos_value (0x%0x) != neg_value (0x%0x)",
                                                        pos_value, neg_value),
                                              $sformatf(" - time=%t", $time)})
  end
  POSEDGE_SAME_VALUE_CHECK_P: assert property (@(check_posedge) pos_value == neg_value) begin
    `uvm_info("POSEDGE_SAME_VALUE_CHECK_P", $sformatf("%m: [i=%0d] - ASSERTION PASSED %t",i, $time),
              UVM_DEBUG);
  end
  else begin
    `uvm_error("POSEDGE_SAME_VALUE_CHECK_P", {$sformatf("%m: [i=%0d] - ASSERTION FAILED",i),
                                              $sformatf(" pos_value (0x%0x) != neg_value (0x%0x)",
                                                        pos_value, neg_value),
                                              $sformatf(" - time=%t", $time)})
  end
end // block: g_signal_stable_sva


endmodule
