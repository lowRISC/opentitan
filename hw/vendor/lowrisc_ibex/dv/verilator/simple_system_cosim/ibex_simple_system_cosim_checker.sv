// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module ibex_simple_system_cosim_checker (
  input clk_i,
  input rst_ni,

  input logic        host_dmem_req,
  input logic        host_dmem_gnt,
  input logic        host_dmem_we,
  input logic [31:0] host_dmem_addr,
  input logic [3:0]  host_dmem_be,
  input logic [31:0] host_dmem_wdata,

  input logic        host_dmem_rvalid,
  input logic [31:0] host_dmem_rdata,
  input logic        host_dmem_err
);
  import "DPI-C" function chandle get_spike_cosim;

  chandle cosim_handle;

  initial begin
    cosim_handle = get_spike_cosim();
  end

  always @(posedge clk_i) begin
    if (u_top.rvfi_valid & !u_top.rvfi_trap) begin
      riscv_cosim_set_nmi(cosim_handle, u_top.rvfi_ext_nmi);
      riscv_cosim_set_mip(cosim_handle, u_top.rvfi_ext_mip);
      riscv_cosim_set_debug_req(cosim_handle, u_top.rvfi_ext_debug_req);
      riscv_cosim_set_mcycle(cosim_handle, u_top.rvfi_ext_mcycle);

      if (riscv_cosim_step(cosim_handle, u_top.rvfi_rd_addr, u_top.rvfi_rd_wdata,
                           u_top.rvfi_pc_rdata, u_top.rvfi_trap) == 0)
      begin
        $display("FAILURE: Co-simulation mismatch at time %t", $time());
        for (int i = 0;i < riscv_cosim_get_num_errors(cosim_handle); ++i) begin
          $display(riscv_cosim_get_error(cosim_handle, i));
        end
        riscv_cosim_clear_errors(cosim_handle);

        $fatal(1, "Co-simulation mismatch seen");
      end
    end
  end

  logic outstanding_store;
  logic [31:0] outstanding_addr;
  logic [3:0] outstanding_be;
  logic [31:0] outstanding_store_data;
  logic outstanding_misaligned_first;
  logic outstanding_misaligned_second;

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      outstanding_store <= 1'b0;
    end else begin
      if (host_dmem_req && host_dmem_gnt) begin
        outstanding_store      <= host_dmem_we;
        outstanding_addr       <= host_dmem_addr;
        outstanding_be         <= host_dmem_be;
        outstanding_store_data <= host_dmem_wdata;
        outstanding_misaligned_first <=
          u_top.u_ibex_top.u_ibex_core.load_store_unit_i.handle_misaligned_d |
          ((u_top.u_ibex_top.u_ibex_core.load_store_unit_i.lsu_type_i == 2'b01) &
           (u_top.u_ibex_top.u_ibex_core.load_store_unit_i.data_offset == 2'b01));

        outstanding_misaligned_second <=
          u_top.u_ibex_top.u_ibex_core.load_store_unit_i.addr_incr_req_o;
      end

      if (host_dmem_rvalid) begin
        riscv_cosim_notify_dside_access(cosim_handle, outstanding_store, outstanding_addr,
          outstanding_store ? outstanding_store_data : host_dmem_rdata, outstanding_be,
          host_dmem_err, outstanding_misaligned_first, outstanding_misaligned_second);
      end
    end
  end
endmodule
