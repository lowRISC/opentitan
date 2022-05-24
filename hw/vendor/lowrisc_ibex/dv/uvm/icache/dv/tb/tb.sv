// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
import ibex_pkg::*;
module tb #(
 parameter bit ICacheECC = 1'b1
 );
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import ibex_icache_env_pkg::*;
  import ibex_icache_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));

  ibex_icache_core_if core_if (.clk(clk), .rst_n(rst_n));
  ibex_icache_mem_if  mem_if  (.clk(clk), .rst_n(rst_n));

  bit           scramble_key_valid, scramble_req;
  logic [127:0] scramble_key;
  logic [63:0]  scramble_nonce;

  localparam int unsigned BusSizeECC  = ICacheECC ? (BUS_SIZE + 7) : BUS_SIZE;
  localparam int unsigned LineSizeECC = BusSizeECC * IC_LINE_BEATS;
  localparam int unsigned TagSizeECC  = ICacheECC ? (IC_TAG_SIZE + 6) : IC_TAG_SIZE;
  localparam int unsigned NumAddrScrRounds  = 2;
  localparam int unsigned NumDiffRounds     = NumAddrScrRounds;

  ibex_icache_ram_if #(
    .TagSizeECC(TagSizeECC),
    .LineSizeECC(LineSizeECC)
  ) ram_if (
    .clk(clk),
    .rst_n(rst_n)
  );

  // Scramble signals
  logic [SCRAMBLE_KEY_W-1:0]      scramble_key_q, scramble_key_d;
  logic [SCRAMBLE_NONCE_W-1:0]    scramble_nonce_q, scramble_nonce_d;
  logic                           scramble_key_valid_d, scramble_key_valid_q;
  logic                           scramble_req_d, scramble_req_q;

  // DUT
  ibex_icache #(
      .ICacheECC       (ICacheECC),
      .BusSizeECC      (BusSizeECC),
      .TagSizeECC      (TagSizeECC),
      .LineSizeECC     (LineSizeECC)
  ) dut (
      .clk_i               ( clk                        ),
      .rst_ni              ( rst_n                      ),

      .req_i               ( core_if.req                ),

      .branch_i            ( core_if.branch             ),
      .addr_i              ( core_if.branch_addr        ),

      .ready_i             ( core_if.ready              ),
      .valid_o             ( core_if.valid              ),
      .rdata_o             ( core_if.rdata              ),
      .addr_o              ( core_if.addr               ),
      .err_o               ( core_if.err                ),
      .err_plus2_o         ( core_if.err_plus2          ),
      .icache_enable_i     ( core_if.enable             ),
      .icache_inval_i      ( core_if.invalidate         ),
      .busy_o              ( core_if.busy               ),

      .instr_req_o         ( mem_if.req                 ),
      .instr_addr_o        ( mem_if.addr                ),
      .instr_gnt_i         ( mem_if.gnt                 ),
      .instr_rvalid_i      ( mem_if.rvalid              ),
      .instr_rdata_i       ( mem_if.rdata               ),
      .instr_err_i         ( mem_if.err                 ),

      .ic_tag_req_o        ( ram_if.ic_tag_req          ),
      .ic_tag_write_o      ( ram_if.ic_tag_write        ),
      .ic_tag_addr_o       ( ram_if.ic_tag_addr         ),
      .ic_tag_wdata_o      ( ram_if.ic_tag_wdata        ),
      .ic_tag_rdata_i      ( ram_if.ic_tag_rdata_o      ),
      .ic_data_req_o       ( ram_if.ic_data_req         ),
      .ic_data_write_o     ( ram_if.ic_data_write       ),
      .ic_data_addr_o      ( ram_if.ic_data_addr        ),
      .ic_data_wdata_o     ( ram_if.ic_data_wdata       ),
      .ic_data_rdata_i     ( ram_if.ic_data_rdata_o     ),
      .ic_scr_key_valid_i  ( scramble_key_valid_q       ),

      // TODO: Probe this and verify functionality
      .ecc_error_o         ( ram_if.ecc_err             )
  );

  // Scramble key valid starts with OTP returning new valid key and stays high
  // until we request a new valid key.
  assign scramble_key_valid_d = scramble_req_q ? scramble_key_valid :
                                core_if.invalidate ? 1'b0           :
                                                 scramble_key_valid_q;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      scramble_key_q       <= 128'hDDDDDDDDEEEEEEEEAAAAAAAADDDDDDDD;
      scramble_nonce_q     <= 64'hBBBBEEEEEEEEFFFF;
    end else if (scramble_key_valid && scramble_req_q) begin
      scramble_key_q       <= scramble_key;
      scramble_nonce_q     <= scramble_nonce;
    end
  end

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      scramble_key_valid_q <= 1'b1;
      scramble_req_q       <= 1'b0;
    end else begin
      scramble_key_valid_q <= scramble_key_valid_d;
      scramble_req_q       <= scramble_req_d;
    end
  end

  // Scramble key request starts with invalidate signal from ICache and stays high
  // until we got a valid key.
  assign scramble_req_d = scramble_req_q ? ~scramble_key_valid : core_if.invalidate;
  assign scramble_req   = scramble_req_q;

  // RAMs
  for (genvar way = 0; way < IC_NUM_WAYS; way++) begin : gen_rams
    // Tag RAM instantiation
    prim_ram_1p_scr #(
      .Width            (TagSizeECC),
      .Depth            (IC_NUM_LINES),
      .DataBitsPerMask  (TagSizeECC),
      .EnableParity     (0),
      .DiffWidth        (TagSizeECC),
      .NumAddrScrRounds (NumAddrScrRounds),
      .NumDiffRounds    (NumDiffRounds)
    ) tag_bank (
      .clk_i       (clk),
      .rst_ni      (rst_n),

      .key_valid_i (scramble_key_valid_q),
      .key_i       (scramble_key_q),
      .nonce_i     (scramble_nonce_q),

      .req_i       (ram_if.ic_tag_req[way]),

      .gnt_o       (),
      .write_i     (ram_if.ic_tag_write),
      .addr_i      (ram_if.ic_tag_addr),
      .wdata_i     (ram_if.ic_tag_wdata),
      .wmask_i     ({TagSizeECC{1'b1}}),
      .intg_error_i(1'b0),

      .rdata_o     (ram_if.ic_tag_rdata_in[way]),
      .rvalid_o    (ram_if.ic_tag_rvalid[way]),
      .raddr_o     (),
      .rerror_o    (),
      .cfg_i       ('0)
    );

    // Data RAM instantiation
    prim_ram_1p_scr #(
      .Width              (LineSizeECC),
      .Depth              (IC_NUM_LINES),
      .DataBitsPerMask    (LineSizeECC),
      .EnableParity       (0),
      .ReplicateKeyStream (1),
      .DiffWidth          (LineSizeECC),
      .NumAddrScrRounds   (NumAddrScrRounds),
      .NumDiffRounds      (NumDiffRounds)
    ) data_bank (
      .clk_i       (clk),
      .rst_ni      (rst_n),

      .key_valid_i (scramble_key_valid_q),
      .key_i       (scramble_key_q),
      .nonce_i     (scramble_nonce_q),

      .req_i       (ram_if.ic_data_req[way]),

      .gnt_o       (),
      .write_i     (ram_if.ic_data_write),
      .addr_i      (ram_if.ic_data_addr),
      .wdata_i     (ram_if.ic_data_wdata),
      .wmask_i     ({LineSizeECC{1'b1}}),
      .intg_error_i(1'b0),

      .rdata_o     (ram_if.ic_data_rdata_in[way]),
      .rvalid_o    (ram_if.ic_data_rvalid[way]),
      .raddr_o     (),
      .rerror_o    (),
      .cfg_i       ('0)
    );
  end


  // Initiate push pull interface for the OTP<->OTBN connections
  push_pull_if #(
    .DeviceDataWidth(194)
  ) scrambling_key_if (
    .clk(clk),
    .rst_n(rst_n)
  );

  // scrambling Key interface assignments
  assign scrambling_key_if.req         = scramble_req;
  // key, nonce, seed_valid all driven by push_pull Device interface
  assign {scramble_key, scramble_nonce, scramble_key_valid} = scrambling_key_if.d_data;

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();

    // Store virtual interfaces into the UVM config database. ECC interfaces are done separately
    // above because otherwise you have to repeat the (verbose) generate loop.
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual ibex_icache_core_if)::set(null, "*.env.core_agent*", "vif", core_if);
    uvm_config_db#(virtual ibex_icache_mem_if)::set(null, "*.env.mem_agent*", "vif", mem_if);
    uvm_config_db#(scrambling_key_vif)::set(
      null, "*.env.scrambling_key_agent*", "vif", scrambling_key_if);

    // Record the number of (ECC) ways in the config database. The top-level environment's config
    // will use this to decide how many agents to create.
    uvm_config_db#(int unsigned)::set(null, "*", "num_ecc_ways", dut.ICacheECC ? ibex_pkg::IC_NUM_WAYS : 0);
    uvm_config_db#(ibex_icache_ram_vif)::set(null, "*.env*", "vif", ram_if);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
