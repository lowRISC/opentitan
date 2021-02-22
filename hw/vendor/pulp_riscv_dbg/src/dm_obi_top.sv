// Copyright 2020 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License").
//
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
//
// You may obtain a copy of the License at:
//
//     https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Arjan Bink - arjan.bink@silabs.com                         //
//                                                                            //
// Design Name:    OBI Wrapper for Debug Module (dm_top)                      //
// Project Name:   CV32E40P                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Wrapper for the Debug Module (dm_top) which gives it an    //
//                 OBI (Open Bus Interface) compatible interfaces so that it  //
//                 can be integrated without further glue logic (other than   //
//                 tie offs in an OBI compliant system.                       //
//                                                                            //
//                 This wrapper is only intended for OBI compliant systems;   //
//                 in other systems the existing dm_top can be used as before //
//                 and this wrapper can be ignored.                           //
//                                                                            //
//                 The OBI spec is available at:                              //
//                                                                            //
//                 - https://github.com/openhwgroup/core-v-docs/blob/master/  //
//                   cores/cv32e40p/                                          //
//                                                                            //
//                 Compared to 'logint' interfaces of dm_top the following    //
//                 signals are added:                                         //
//                                                                            //
//                 - slave_* OBI interface:                                   //
//                                                                            //
//                   - slave_gnt_o                                            //
//                   - slave_rvalid_o                                         //
//                   - slave_aid_i                                            //
//                   - slave_rid_o                                            //
//                                                                            //
//                 Compared to 'logint' interfaces of dm_top the following    //
//                 signals have been renamed:                                 //
//                                                                            //
//                 - master_* OBI interface:                                  //
//                                                                            //
//                   - Renamed master_add_o to master_addr_o                  //
//                   - Renamed master_r_valid_i to master_rvalid_i            //
//                   - Renamed master_r_rdata_i to master_rdata_i             //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module dm_obi_top #(
  parameter int unsigned        IdWidth          = 1,      // Width of aid/rid
  parameter int unsigned        NrHarts          = 1,
  parameter int unsigned        BusWidth         = 32,
  parameter int unsigned        DmBaseAddress    = 'h1000, // default to non-zero page
  // Bitmask to select physically available harts for systems
  // that don't use hart numbers in a contiguous fashion.
  parameter logic [NrHarts-1:0] SelectableHarts  = {NrHarts{1'b1}}
) (
  input  logic                  clk_i,           // clock
  // asynchronous reset active low, connect PoR here, not the system reset
  input  logic                  rst_ni,
  input  logic                  testmode_i,
  output logic                  ndmreset_o,      // non-debug module reset
  output logic                  dmactive_o,      // debug module is active
  output logic [NrHarts-1:0]    debug_req_o,     // async debug request
  // communicate whether the hart is unavailable (e.g.: power down)
  input  logic [NrHarts-1:0]    unavailable_i,
  input  dm::hartinfo_t [NrHarts-1:0]  hartinfo_i,

  input  logic                  slave_req_i,
  // OBI grant for slave_req_i (not present on dm_top)
  output logic                  slave_gnt_o,
  input  logic                  slave_we_i,
  input  logic [BusWidth-1:0]   slave_addr_i,
  input  logic [BusWidth/8-1:0] slave_be_i,
  input  logic [BusWidth-1:0]   slave_wdata_i,
  // Address phase transaction identifier (not present on dm_top)
  input  logic [IdWidth-1:0]    slave_aid_i,
  // OBI rvalid signal (end of response phase for reads/writes) (not present on dm_top)
  output logic                  slave_rvalid_o,
  output logic [BusWidth-1:0]   slave_rdata_o,
  // Response phase transaction identifier (not present on dm_top)
  output logic [IdWidth-1:0]    slave_rid_o,

  output logic                  master_req_o,
  output logic [BusWidth-1:0]   master_addr_o,   // Renamed according to OBI spec
  output logic                  master_we_o,
  output logic [BusWidth-1:0]   master_wdata_o,
  output logic [BusWidth/8-1:0] master_be_o,
  input  logic                  master_gnt_i,
  input  logic                  master_rvalid_i, // Renamed according to OBI spec
  input  logic [BusWidth-1:0]   master_rdata_i,  // Renamed according to OBI spec

  // Connection to DTM - compatible to RocketChip Debug Module
  input  logic                  dmi_rst_ni,
  input  logic                  dmi_req_valid_i,
  output logic                  dmi_req_ready_o,
  input  dm::dmi_req_t          dmi_req_i,

  output logic                  dmi_resp_valid_o,
  input  logic                  dmi_resp_ready_i,
  output dm::dmi_resp_t         dmi_resp_o
);

  // Slave response phase (rvalid and identifier)
  logic               slave_rvalid_q;
  logic [IdWidth-1:0] slave_rid_q;

  // dm_top instance
  dm_top #(
    .NrHarts                 ( NrHarts               ),
    .BusWidth                ( BusWidth              ),
    .DmBaseAddress           ( DmBaseAddress         ),
    .SelectableHarts         ( SelectableHarts       )
  ) i_dm_top (
    .clk_i                   ( clk_i                 ),
    .rst_ni                  ( rst_ni                ),
    .testmode_i              ( testmode_i            ),
    .ndmreset_o              ( ndmreset_o            ),
    .dmactive_o              ( dmactive_o            ),
    .debug_req_o             ( debug_req_o           ),
    .unavailable_i           ( unavailable_i         ),
    .hartinfo_i              ( hartinfo_i            ),

    .slave_req_i             ( slave_req_i           ),
    .slave_we_i              ( slave_we_i            ),
    .slave_addr_i            ( slave_addr_i          ),
    .slave_be_i              ( slave_be_i            ),
    .slave_wdata_i           ( slave_wdata_i         ),
    .slave_rdata_o           ( slave_rdata_o         ),

    .master_req_o            ( master_req_o          ),
    .master_add_o            ( master_addr_o         ), // Renamed according to OBI spec
    .master_we_o             ( master_we_o           ),
    .master_wdata_o          ( master_wdata_o        ),
    .master_be_o             ( master_be_o           ),
    .master_gnt_i            ( master_gnt_i          ),
    .master_r_valid_i        ( master_rvalid_i       ), // Renamed according to OBI spec
    .master_r_rdata_i        ( master_rdata_i        ), // Renamed according to OBI spec

    .dmi_rst_ni              ( dmi_rst_ni            ),
    .dmi_req_valid_i         ( dmi_req_valid_i       ),
    .dmi_req_ready_o         ( dmi_req_ready_o       ),
    .dmi_req_i               ( dmi_req_i             ),

    .dmi_resp_valid_o        ( dmi_resp_valid_o      ),
    .dmi_resp_ready_i        ( dmi_resp_ready_i      ),
    .dmi_resp_o              ( dmi_resp_o            )
  );

  // Extension to wrap dm_top as an OBI-compliant module
  //
  // dm_top has an implied rvalid pulse the cycle after its granted request.

  // Registers
  always_ff @(posedge clk_i or negedge rst_ni) begin : obi_regs
    if (!rst_ni) begin
      slave_rvalid_q   <= 1'b0;
      slave_rid_q      <= 'b0;
    end else begin
      if (slave_req_i && slave_gnt_o) begin // 1 cycle pulse on rvalid for every granted request
        slave_rvalid_q <= 1'b1;
        slave_rid_q    <= slave_aid_i;      // Mirror aid to rid
      end else begin
        slave_rvalid_q <= 1'b0;             // rid is don't care if rvalid = 0
      end
    end
  end

  assign slave_gnt_o = 1'b1;                // Always receptive to request (slave_req_i)
  assign slave_rvalid_o = slave_rvalid_q;
  assign slave_rid_o = slave_rid_q;

endmodule : dm_obi_top
