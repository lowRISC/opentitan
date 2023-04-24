// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// -------- W A R N I N G: A U T O - G E N E R A T E D  C O D E !! -------- //
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED.
//
//############################################################################
// *Name: dev_entropy
// *Module Description:  Device Entropy
//############################################################################

module dev_entropy #(
  parameter int EntropyRateWidth = 4
) (
  input clk_i,                              // Entropy Clock
  input rst_ni,                             // Entropy Reset
  input clk_dev_i,                          // Device Clock
  input rst_dev_ni,                         // Device Reset
  input dev_en_i,                           // Device Enable
  input [EntropyRateWidth-1:0] dev_rate_i,  // Entropy Rate
  input dev_ack_i,                          // Write Valid (EDN_ACK)
  input [32-1:0] dev_data_i,                // Write Data (EDN_BUS)
  output logic dev_wready_o,                // Write Ready (EDN_REQ)
  output logic dev_data_o                   // Entropy Data
);


////////////////////////////////////
// Device Enable Sync
////////////////////////////////////
logic dev_en_dev;

// Sync dev_en to Dev clock
prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_dev_en_dev_sync (
  .clk_i ( clk_dev_i ),
  .rst_ni ( rst_dev_ni ),
  .d_i ( dev_en_i ),
  .q_o ( dev_en_dev )
);


////////////////////////////////////
// Entropy Rate
///////////////////////////////////////
logic fast_start, rate_pulse, rready;
logic [7-1:0] fast_cnt;
logic [(1<<EntropyRateWidth)-1:0] erate_cnt, dev_rate;

// Sync dev_rate_i to Device clock
logic [EntropyRateWidth-1:0] dev_rate_sync;

prim_multibit_sync #(
  .Width ( EntropyRateWidth ),
  .ResetValue ( {EntropyRateWidth{1'b0}} )
) u_erate_sync (
  .clk_i ( clk_dev_i ) ,
  .rst_ni ( rst_dev_ni ),
  .data_i ( dev_rate_i[EntropyRateWidth-1:0] ),
  .data_o ( dev_rate_sync[EntropyRateWidth-1:0] )
);

// Fastest rate to init the LFSR
always_ff @( posedge clk_dev_i, negedge rst_dev_ni ) begin
  if ( !rst_dev_ni ) begin
    fast_start <= 1'b1;
    fast_cnt   <= 7'h00;
  end else if ( fast_cnt == 7'h40 ) begin
    fast_start <= 1'b0;
  end else if ( fast_start && rready ) begin
    fast_cnt   <= fast_cnt + 1'b1;
  end
end

assign dev_rate = fast_start ? '0 : ((1<<EntropyRateWidth)'(1'b1) << dev_rate_sync) - 1;

always_ff @( posedge clk_dev_i, negedge rst_dev_ni ) begin
  if ( !rst_dev_ni ) begin
    erate_cnt <= '0;
  end else if ( rate_pulse ) begin
    erate_cnt <= dev_rate;
  end else if ( erate_cnt != '0 ) begin
    erate_cnt <= erate_cnt - 1'b1;
  end
end

assign rate_pulse = (erate_cnt == '0) && dev_en_dev;


////////////////////////////////////////
// Entropy Data Buffer at ES Clock
////////////////////////////////////////

// Entropy Clock
///////////////////////////////////////
logic [32-1:0] wdata;

always_ff @( posedge clk_i, negedge rst_ni ) begin
  if ( !rst_ni ) begin
    wdata <= 32'h0000_0000;
  end else if ( dev_ack_i ) begin
    wdata <= dev_data_i;
  end
end

// Sync wvalid to ES clock
logic wready_dev, wready_es;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_wvalid_es_sync (
  .clk_i,
  .rst_ni,
  .d_i ( wready_dev ),
  .q_o ( wready_es )
);

logic wready_es_d;

always_ff @( posedge clk_i, negedge rst_ni ) begin
  if ( !rst_ni ) begin
    wready_es_d <= 1'b0;
  end else begin
    wready_es_d <= wready_es;
  end
end

logic wdata_val, set_wdata_val, clr_wdata_val, wready_es_fe;

assign wready_es_fe  = !wready_es && wready_es_d;
assign set_wdata_val = !wdata_val && dev_ack_i;
assign clr_wdata_val =  wdata_val && wready_es_fe;

always_ff @( posedge clk_i, negedge rst_ni ) begin
  if ( !rst_ni ) begin
    wdata_val <= 1'b0;
  end else if ( set_wdata_val ) begin
    wdata_val <= 1'b1;
  end else if ( clr_wdata_val ) begin
    wdata_val <= 1'b0;
  end
end

assign dev_wready_o = !wdata_val;


// Device Clock
///////////////////////////////////////
// Reset de-assert of rst_ni to Device clock
logic rst_es_dev_in_n, rst_es_dev_da_n, rst_es_dev_n;

assign rst_es_dev_in_n = rst_ni && rst_dev_ni;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_rst_es_n_da (
  .clk_i ( clk_dev_i ),
  .rst_ni ( rst_es_dev_in_n ),
  .d_i ( 1'b1 ),
  .q_o ( rst_es_dev_da_n )
);

assign rst_es_dev_n = rst_es_dev_da_n;

// Sync wready_es to Device clock
logic wready, wready_es_dev;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_wready_es_dev_sync (
  .clk_i ( clk_dev_i ),
  .rst_ni ( rst_es_dev_n ),
  .d_i ( wready_es ),
  .q_o ( wready_es_dev )
);

logic set_wready_dev, clr_wready_dev;

assign set_wready_dev = !wready_dev && wready;
assign clr_wready_dev =  wready_dev && !wready && wready_es_dev;

always_ff @( posedge clk_dev_i, negedge rst_es_dev_n ) begin
  if ( !rst_es_dev_n ) begin
    wready_dev <= 1'b0;
  end else if ( set_wready_dev ) begin
    wready_dev <= 1'b1;
  end else if ( clr_wready_dev ) begin
    wready_dev <= 1'b0;
  end
end

// Sync wdata_val to Device clock
logic wdata_val_dev;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_wvalid_dev_sync (
  .clk_i ( clk_dev_i ),
  .rst_ni ( rst_es_dev_n ),
  .d_i ( wdata_val ),
  .q_o ( wdata_val_dev )
);

logic wvalid, set_wvalid, clr_wvalid;

assign set_wvalid = !wvalid && wready && wdata_val_dev;
assign clr_wvalid =  wvalid;

always_ff @( posedge clk_dev_i, negedge rst_es_dev_n ) begin
  if ( !rst_es_dev_n ) begin
    wvalid <= 1'b0;
  end else if ( set_wvalid ) begin
    wvalid <= 1'b1;
  end else if ( clr_wvalid ) begin
    wvalid <= 1'b0;
  end
end


////////////////////////////////////////
// Packer FIFO (32to1 bit)
////////////////////////////////////////
logic rdata, rvalid;
logic [6-1:0] depth;

prim_packer_fifo #(
  .InW ( 32 ),
  .OutW ( 1 )
) u_dev_fifo (
  .clk_i ( clk_dev_i ),
  .rst_ni ( rst_dev_ni ),
  .clr_i ( 1'b0 ),            // !dev_en_dev ), // Clear (sync)
  .wvalid_i ( wvalid ),       // Write Valid
  .wdata_i ( wdata ),         // Write Data (32-bit)
  .wready_o ( wready ),       // Write Ready
  //
  .rvalid_o ( rvalid ),       // Read Valid
  .rdata_o ( rdata ),         // Read Data
  .rready_i ( rready ),       // Read Ready (done)
  .depth_o ( depth[6-1:0] )   // empty when (depth_o == `0)
);

assign rready     = rvalid && rate_pulse;
assign dev_data_o = rdata && rate_pulse;


///////////////////////
// Unused Signals
///////////////////////
logic unused_sigs;
assign unused_sigs = ^{ depth[6-1:0] };

endmodule : dev_entropy
