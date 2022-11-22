/* Copyright 2018 ETH Zurich and University of Bologna.
* Copyright and related rights are licensed under the Solderpad Hardware
* License, Version 0.51 (the “License”); you may not use this file except in
* compliance with the License.  You may obtain a copy of the License at
* http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
* or agreed to in writing, software, hardware and materials distributed under
* this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
* CONDITIONS OF ANY KIND, either express or implied. See the License for the
* specific language governing permissions and limitations under the License.
*
* File:   axi_riscv_debug_module.sv
* Author: Andreas Traber <atraber@iis.ee.ethz.ch>
* Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
*
* Description: Clock domain crossings for JTAG to DMI very heavily based
*              on previous work by Andreas Traber for the PULP project.
*              This is mainly a wrapper around the existing CDCs.
*/
module dmi_cdc (
  // Test controls
  input  logic             testmode_i,
  input  logic             test_rst_ni,

  // JTAG side (master side)
  input  logic             tck_i,
  input  logic             trst_ni,
  input  dm::dmi_req_t     jtag_dmi_req_i,
  output logic             jtag_dmi_ready_o,
  input  logic             jtag_dmi_valid_i,
  input  logic             jtag_dmi_cdc_clear_i, // Synchronous clear signal.
                                                 // Triggers reset sequencing
                                                 // accross CDC

  output dm::dmi_resp_t    jtag_dmi_resp_o,
  output logic             jtag_dmi_valid_o,
  input  logic             jtag_dmi_ready_i,

  // core side (slave side)
  input  logic             clk_i,
  input  logic             rst_ni,

  output logic             core_dmi_rst_no,
  output dm::dmi_req_t     core_dmi_req_o,
  output logic             core_dmi_valid_o,
  input  logic             core_dmi_ready_i,

  input dm::dmi_resp_t     core_dmi_resp_i,
  output logic             core_dmi_ready_o,
  input  logic             core_dmi_valid_i
);


  // TODO: Make it clean for synthesis.
  logic jtag_combined_rstn;
  always_ff @(posedge tck_i or negedge trst_ni) begin
    if (!trst_ni) begin
      jtag_combined_rstn <= '0;
    end else if (jtag_dmi_cdc_clear_i) begin
      jtag_combined_rstn <= '0;
    end else begin
      jtag_combined_rstn <= 1'b1;
    end
  end

  logic combined_rstn_premux;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue(0)
  ) u_combined_rstn_sync (
    .clk_i,
    .rst_ni(rst_ni & jtag_combined_rstn),
    .d_i(1'b1),
    .q_o(combined_rstn_premux)
  );

  logic combined_rstn;
  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_rst_mux (
    .clk0_i(combined_rstn_premux),
    .clk1_i(test_rst_ni),
    .sel_i(testmode_i),
    .clk_o(combined_rstn)
  );

  prim_fifo_async_simple #(
    .Width($bits(dm::dmi_req_t)),
    // Use the RZ protocol so that the two sides can be reset independently without getting
    // out of sync due to EVEN/ODD states.
    .EnRzHs(1)
  ) i_cdc_req (
    .clk_wr_i (tck_i),
    .rst_wr_ni(trst_ni),
    .wvalid_i (jtag_dmi_valid_i),
    .wready_o (jtag_dmi_ready_o),
    .wdata_i  (jtag_dmi_req_i),
    .clk_rd_i (clk_i),
    .rst_rd_ni(combined_rstn),
    .rvalid_o (core_dmi_valid_o),
    .rready_i (core_dmi_ready_i),
    .rdata_o  (core_dmi_req_o)
  );

  prim_fifo_async_simple #(
    .Width($bits(dm::dmi_resp_t)),
    // Use the RZ protocol so that the two sides can be reset independently without getting
    // out of sync due to EVEN/ODD states.
    .EnRzHs(1)
  ) i_cdc_resp (
    .clk_wr_i (clk_i),
    .rst_wr_ni(combined_rstn),
    .wvalid_i (core_dmi_valid_i),
    .wready_o (core_dmi_ready_o),
    .wdata_i  (core_dmi_resp_i),
    .clk_rd_i (tck_i),
    .rst_rd_ni(trst_ni),
    .rvalid_o (jtag_dmi_valid_o),
    .rready_i (jtag_dmi_ready_i),
    .rdata_o  (jtag_dmi_resp_o)
  );

  assign core_dmi_rst_no = combined_rstn;

endmodule : dmi_cdc
