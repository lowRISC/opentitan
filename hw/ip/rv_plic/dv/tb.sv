// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module tb;

  import uvm_pkg::*;
  import tlul_pkg::*;
  import plic_pkg::*;

  logic clk;
  logic rst_n;

  localparam ClkPeriod = 10ns;
  localparam int N_SOURCE=32;
  localparam int SRCW = $clog2(N_SOURCE+1);
  localparam int N_TARGET=1;

  tlul_if intc_reg_if(clk, rst_n);

  plic_if #(.N_SOURCE(N_SOURCE)) irq_if(clk, rst_n);

  initial begin
    uvm_config_db#(virtual tlul_if)::set(null,"*","vif", intc_reg_if);
    uvm_config_db#(virtual plic_if)::set(null,"*","pif", irq_if);
    uvm_config_db#(logic [31:0])::set(null,"*","plic_base_address", 32'h0000_0000);
    uvm_config_db#(int)::set(null,"*","num_source", N_SOURCE);
    uvm_config_db#(int)::set(null,"*","num_target", N_TARGET);
    uvm_config_db#(int)::set(null,"*","max_priority", 7);
  end

  initial begin
    run_test();
  end


  logic [N_SOURCE-1:0] intr_src;
  logic                intr_irq [N_TARGET];
  logic [SRCW-1:0]     intr_id  [N_TARGET];

  assign irq_if.dut.irq = intr_irq[0];
  assign irq_if.dut.irq_id = intr_id[0];

  // clk & reset
  initial begin
    clk = 1'b0;
    forever begin
      #(ClkPeriod/2) clk=~clk;
    end
  end

  initial begin
    rst_n = 1'b0;
    repeat(3) @(negedge clk);
    rst_n = 1'b1;
  end

  // Sim hard finish
  initial begin
    #100us
    $finish(1);
  end

  rv_plic #(
    .N_SOURCE(N_SOURCE),
    .N_TARGET(N_TARGET)
  ) dut (
    .clk_i  (clk),
    .rst_ni (rst_n),

    .tl_i   (intc_reg_if.device.h2d),
    .tl_o   (intc_reg_if.device.d2h),

    .intr_src_i (intr_src),

    .irq_o    (intr_irq),
    .irq_id_o (intr_id)
  );

  initial begin
    intr_src = 0;

    intr_src = $urandom();
    #1us
    @(posedge clk);
  end

endmodule
