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
  // JTAG side (master side)
  input  logic             tck_i,
  input  logic             trst_ni,

  input  dm::dmi_req_t     jtag_dmi_req_i,
  output logic             jtag_dmi_ready_o,
  input  logic             jtag_dmi_valid_i,

  output dm::dmi_resp_t    jtag_dmi_resp_o,
  output logic             jtag_dmi_valid_o,
  input  logic             jtag_dmi_ready_i,

  // core side (slave side)
  input  logic             clk_i,
  input  logic             rst_ni,

  output dm::dmi_req_t     core_dmi_req_o,
  output logic             core_dmi_valid_o,
  input  logic             core_dmi_ready_i,

  input dm::dmi_resp_t     core_dmi_resp_i,
  output logic             core_dmi_ready_o,
  input  logic             core_dmi_valid_i
);

  // TODO: Make it clean for synthesis.

  prim_fifo_async #(
    .Width       ( $bits(dm::dmi_req_t) ),
    .Depth       ( 4 )
  ) i_cdc_req (
    .clk_wr_i    ( tck_i            ),
    .rst_wr_ni   ( trst_ni          ),
    .wvalid_i    ( jtag_dmi_valid_i ),
    .wready_o    ( jtag_dmi_ready_o ), // wrclk
    .wdata_i     ( jtag_dmi_req_i   ),
    .wdepth_o    (                  ),

    .clk_rd_i    ( clk_i            ),
    .rst_rd_ni   ( rst_ni           ),
    .rvalid_o    ( core_dmi_valid_o ),
    .rready_i    ( core_dmi_ready_i ),
    .rdata_o     ( core_dmi_req_o   ),
    .rdepth_o    (                  )
  );

  prim_fifo_async #(
    .Width       ( $bits(dm::dmi_resp_t) ),
    .Depth       ( 4 )
  ) i_cdc_resp (
    .clk_wr_i    ( clk_i            ),
    .rst_wr_ni   ( rst_ni           ),
    .wvalid_i    ( core_dmi_valid_i ),
    .wready_o    ( core_dmi_ready_o ), // wrclk
    .wdata_i     ( core_dmi_resp_i  ),
    .wdepth_o    (                  ),

    .clk_rd_i    ( tck_i            ),
    .rst_rd_ni   ( trst_ni          ),
    .rvalid_o    ( jtag_dmi_valid_o ),
    .rready_i    ( jtag_dmi_ready_i ),
    .rdata_o     ( jtag_dmi_resp_o  ),
    .rdepth_o    (                  )
  );

endmodule : dmi_cdc
