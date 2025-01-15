// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

import uvm_pkg::*;

module spi_host_data_stable_sva #(
  parameter int unsigned NumCS = 1
) (
  input logic                                              rst_ni,
  input logic                                              cio_sck_o,
  input logic [NumCS-1:0]                                  cio_csb_o,
  input logic [3:0]                                        cio_sd_i,
  input logic [3:0]                                        cio_sd_en_o,
  input spi_host_reg_pkg::spi_host_reg2hw_configopts_reg_t configopts,
  input spi_device_pkg::passthrough_req_t                  passthrough_i
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
     .sck_o (cio_sck_o),
     .csb_o (csbs),
     .signal2check_i (cio_sd_i),
     .sampled_negedge_enable (sampled_negedge_enable),
     .sampled_posedge_enable (sampled_posedge_enable),
     .passthrough_en (passthrough_i.passthrough_en)
     );

  whole_cycle_data_stable_signal_checker #(.VECTOR_WIDTH(4))
  u_sva_cio_sd_en_o_whole_cycle_data_stable_check (
     .rst_ni (rst_ni),
     .sck_o (cio_sck_o),
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


  for (genvar i = 0; i < VECTOR_WIDTH; i++) begin : g_signal_stable_sva
    logic neg_value, pos_value;

    // Always_ff below are used just for the printout in case of the SVA firing
    always_ff @(negedge sck_o) begin
      neg_value <= signal2check_i[i];
    end // always_ff @ (negedge sck_o)
    always_ff @(posedge sck_o) begin
      pos_value <= signal2check_i[i];
    end // always_ff @ (posedge sck_o)

    // The data bus is driven on one edge and sampled on the next. Hence the value can't
    // toggle in the "sample phase"
    property posedge_no_change_check_p;
      @(posedge sck_o) disable iff (rst_ni)
        sampled_posedge_enable |-> !$changed(signal2check_i[i]);
    endproperty

    property negedge_no_change_check_p;
      @(negedge sck_o) disable iff (rst_ni)
        sampled_negedge_enable |-> !$changed(signal2check_i[i]);
    endproperty

    NEGEDGE_SAME_VALUE_CHECK_P: assert property (negedge_no_change_check_p)
    else begin
      uvm_report_error("NEGEDGE_SAME_VALUE_CHECK_P",
                       {$sformatf("%m: [i=%0d] - ASSERTION FAILED",i),
                        $sformatf(" pos_value (0x%0x) != neg_value (0x%0x)",
                                  $sampled(pos_value), $sampled(neg_value)),
                        $sformatf(" - time=%t", $time)});
    end

    POSEDGE_SAME_VALUE_CHECK_P: assert property (posedge_no_change_check_p)
    else begin
       uvm_report_error("POSEDGE_SAME_VALUE_CHECK_P",
                        {$sformatf("%m: [i=%0d] - ASSERTION FAILED",i),
                         $sformatf(" pos_value (0x%0x) != neg_value (0x%0x)",
                                   $sampled(pos_value), $sampled(neg_value)),
                         $sformatf(" - time=%t", $time)});
    end
  end // block: g_signal_stable_sva

endmodule
