// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module tb;

  import uvm_pkg::*;
  import rjtag_pkg::*;

  localparam int NrHarts = 1;
  localparam int ClkPeriod = 10;  // 10ns

  logic clk;
  logic rst_n;
  logic ndmrst;
  logic dmactive;
  logic [NrHarts-1:0] debug_req;
  logic [NrHarts-1:0] unavailable;

  xbar_if tlul_mem_if (clk);
  xbar_if tlul_dm_if (clk);

  // clk & reset
  initial begin
    clk = 1'b0;
    forever begin
      #(ClkPeriod / 2) clk = ~clk;
    end
  end

  initial begin
    rst_n = 1'b0;
    repeat (3) @(negedge clk);
    rst_n = 1'b1;
  end

  initial begin
    #100us $finish(1);
  end

  logic clk_jtag, rst_jtag_n;

  jtag_if jtag ();

  initial begin
    uvm_config_db#(virtual jtag_if)::set(null, "*", "vif", jtag);
  end

  initial begin
    run_test();
  end


  dm::dmi_req_t dmi_req;
  dm::dmi_resp_t dmi_rsp;

  // Device SRAM:
  device_sram sram;
  initial begin
    sram = new(0);
    sram.connect(tlul_dm_if.device);

    sram.run();
  end

  rv_dm #(
      .NrHarts(NrHarts),
      .AxiIdWidth(8),
      .AxiAddrWidth(32),
      .AxiDataWidth(32),
      .AxiUserWidth(16)
  ) u_dm_top (
      .clk_i        (clk),  // in clock
      // in asynchronous reset active low, connect PoR here, not the system reset
      .rst_ni       (rst_n),
      .testmode_i   (1'b0),  // in
      .ndmreset_o   (ndmrst),  // out               non-debug module reset
      .dmactive_o   (dmactive),  // out               debug module is active
      .debug_req_o  (debug_req),  // out [NrHarts-1:0] async debug request
      // in  [NrHarts-1:0] communicate whether the hart is unavailable (e.g.: power down)
      .unavailable_i(unavailable),

      // bus device, for an execution based technique
      //.tl_d_i        (tlul_mem_if.device.h2d),
      //.tl_d_o        (tlul_mem_if.host.h2d),

      // bus host, for system bus accesses
      .tl_h_o(tlul_dm_if.host.h2d),
      .tl_h_i(tlul_dm_if.host.d2h),

      // Connection to DTM - compatible to RocketChip Debug Module
      .dmi_rst_ni     (dmi_rst_n),
      .dmi_req_valid_i(dmi_req_valid),
      .dmi_req_ready_o(dmi_req_ready),
      .dmi_req_i      (dmi_req),

      .dmi_resp_valid_o(dmi_rsp_valid),
      .dmi_resp_ready_i(dmi_rsp_ready),
      .dmi_resp_o      (dmi_rsp)
  );

  dmi_jtag dap (
      .clk_i     (clk),
      .rst_ni    (rst_n),
      .testmode_i(1'b0),

      .dmi_rst_no     (dmi_rst_n),
      .dmi_req_o      (dmi_req),
      .dmi_req_valid_o(dmi_req_valid),
      .dmi_req_ready_i(dmi_req_ready),

      .dmi_resp_i      (dmi_rsp),
      .dmi_resp_ready_o(dmi_rsp_ready),
      .dmi_resp_valid_i(dmi_rsp_valid),

      //JTAG
      .tck_i   (jtag.dut.tck),
      .tms_i   (jtag.dut.tms),
      .trst_ni (jtag.dut.trst_n),
      .td_i    (jtag.dut.tdi),
      .td_o    (jtag.dut.tdo),
      .tdo_oe_o(jtag.dut.tdo_oe)
  );

  localparam time JtckPeriod = 27.3ns;
  initial begin
    jtag.tb.tck = 0;
    forever begin
      #(JtckPeriod / 2) jtag.tb.tck = ~jtag.tb.tck;
    end
  end
  initial begin
    jtag.tb.trst_n = 1'b0;
    #50ns;
    jtag.tb.trst_n = 1'b1;
  end

endmodule
