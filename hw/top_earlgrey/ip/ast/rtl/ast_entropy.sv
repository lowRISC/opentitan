// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// -------- W A R N I N G: A U T O - G E N E R A T E D  C O D E !! -------- //
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED.
//
//############################################################################
// *Name: ast_entropy
// *Module Description:  AST Entropy
//############################################################################

module ast_entropy #(
  parameter int EntropyRateWidth = 4
) (
  input edn_pkg::edn_rsp_t entropy_rsp_i,          // Entropy Response
  input [EntropyRateWidth-1:0] entropy_rate_i,     // Entropy Rate
  input clk_ast_es_i,                              // Entropy Clock
  input rst_ast_es_ni,                             // Entropy Reset
  input clk_src_sys_i,                             // System Source Clock
  input rst_src_sys_ni,                            // System Source Reset
  input clk_src_sys_val_i,                         // System Source Clock Valid
  input clk_src_sys_jen_i,                         // System Source Clock Jitter Enable
  output edn_pkg::edn_req_t entropy_req_o          // Entropy Request
);

////////////////////////////////////////
// Entropy Request FSM
////////////////////////////////////////
typedef enum logic [2-1:0] {
  ERQ_REQ0 = 2'd1,  // Device-0 Request (source)
  ERQ_ACK0 = 2'd3,  // Device-0 Acknowledge
  ERQ_IDLE = 2'd0   // IDLE/RESET
} erq_sm_e;

erq_sm_e erq_sm;
logic dev0_wready, dev0_ack;
logic edn_ack, edn_req;
logic [32-1:0] edn_bus;

// Pack/Un-pack
assign entropy_req_o.edn_req = edn_req;
assign edn_ack = entropy_rsp_i.edn_ack;
assign edn_bus = entropy_rsp_i.edn_bus;

always_ff @( posedge clk_ast_es_i, negedge rst_ast_es_ni ) begin
  if ( !rst_ast_es_ni ) begin
    edn_req <= 1'b0;
    erq_sm  <= ERQ_IDLE;
  end else begin
    unique case ( erq_sm )
      ERQ_IDLE: begin
        if ( dev0_wready ) begin
          edn_req <= 1'b1;
          erq_sm  <= ERQ_REQ0;
        end else begin
          edn_req <= 1'b0;
          erq_sm  <= ERQ_IDLE;
        end
      end

      ERQ_REQ0: begin
        if ( edn_ack ) begin
          edn_req <= 1'b0;
          erq_sm  <= ERQ_ACK0;
        end else begin
          edn_req <= 1'b1;
          erq_sm  <= ERQ_REQ0;
        end
      end

      ERQ_ACK0: begin
        if ( dev0_wready ) begin
          edn_req <= 1'b1;
          erq_sm  <= ERQ_REQ0;
        end else begin
          edn_req <= 1'b0;
          erq_sm  <= ERQ_ACK0;
        end
      end

      default: begin
        edn_req <= 1'b0;
        erq_sm  <= ERQ_IDLE;
      end
    endcase
  end
end

assign dev0_ack = edn_ack && ((erq_sm == ERQ_REQ0) || (erq_sm == ERQ_ACK0));


////////////////////////////////////////
// Device 0
////////////////////////////////////////
logic dev0_en, dev0_entropy;

assign dev0_en = clk_src_sys_val_i && clk_src_sys_jen_i;

dev_entropy #(
  .EntropyRateWidth ( EntropyRateWidth )
) u_dev0_entropy (
  .clk_i ( clk_ast_es_i ),
  .rst_ni ( rst_ast_es_ni ),
  .clk_dev_i ( clk_src_sys_i ),
  .rst_dev_ni ( rst_src_sys_ni ),
  .dev_en_i ( dev0_en ),
  .dev_rate_i ( entropy_rate_i[EntropyRateWidth-1:0] ),
  .dev_ack_i ( dev0_ack ),
  .dev_data_i ( edn_bus[32-1:0] ),
  .dev_wready_o ( dev0_wready ),
  .dev_data_o ( dev0_entropy )
);



/////////////////////
// Unused Signals
/////////////////////
logic unused_sigs;
assign unused_sigs = ^{ entropy_rsp_i.edn_fips,
                        dev0_entropy              // Used in ASIC implementation
                      };

endmodule : ast_entropy
