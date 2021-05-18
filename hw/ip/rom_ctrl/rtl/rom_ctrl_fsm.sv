// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// The ROM checker FSM module
//

module rom_ctrl_fsm
  import prim_util_pkg::vbits;
#(
  parameter int RomDepth = 16,
  parameter int TopCount = 8,
  parameter bit SkipCheck = 1'b0
) (
  input logic                        clk_i,
  input logic                        rst_ni,

  // CSR inputs for DIGEST and EXP_DIGEST. To make the indexing look nicer, these are ordered so
  // that DIGEST_0 is the bottom 32 bits (they get reversed while we're shuffling around the wires
  // in rom_ctrl).
  input logic [TopCount*32-1:0]      digest_i,
  input logic [TopCount*32-1:0]      exp_digest_i,

  // CSR outputs for DIGEST and EXP_DIGEST. Ordered with word 0 as LSB.
  output logic [TopCount*32-1:0]     digest_o,
  output logic                       digest_vld_o,
  output logic [31:0]                exp_digest_o,
  output logic                       exp_digest_vld_o,
  output logic [vbits(TopCount)-1:0] exp_digest_idx_o,

  // To power manager and key manager
  output rom_ctrl_pkg::pwrmgr_data_t pwrmgr_data_o,
  output rom_ctrl_pkg::keymgr_data_t keymgr_data_o,

  // To KMAC (ROM data)
  input logic                        kmac_rom_rdy_i,
  output logic                       kmac_rom_vld_o,
  output logic                       kmac_rom_last_o,

  // To KMAC (digest data)
  input logic                        kmac_done_i,
  input logic [TopCount*32-1:0]      kmac_digest_i,

  // To ROM mux
  output logic                       rom_select_o,
  output logic [vbits(RomDepth)-1:0] rom_addr_o,
  output logic                       rom_req_o,

  // Raw bits from ROM
  input logic [31:0]                 rom_data_i,

  // To alert system
  output logic                       alert_o
);

  localparam int AW = vbits(RomDepth);
  localparam int TAW = vbits(TopCount);

  localparam int unsigned TopStartAddrInt = RomDepth - TopCount;
  localparam bit [AW-1:0] TopStartAddr    = TopStartAddrInt[AW-1:0];

  // The counter / address generator
  logic          counter_done;
  logic [AW-1:0] counter_read_addr;
  logic          counter_read_req;
  logic [AW-1:0] counter_data_addr;
  logic          counter_data_rdy, counter_data_vld;
  logic          counter_lnt;
  rom_ctrl_counter #(
    .RomDepth (RomDepth),
    .RomTopCount (TopCount)
  ) u_counter (
    .clk_i              (clk_i),
    .rst_ni             (rst_ni),
    .done_o             (counter_done),
    .read_addr_o        (counter_read_addr),
    .read_req_o         (counter_read_req),
    .data_addr_o        (counter_data_addr),
    .data_rdy_i         (counter_data_rdy),
    .data_vld_o         (counter_data_vld),
    .data_last_nontop_o (counter_lnt)
  );

  // The compare block (responsible for comparing CSR data and forwarding it to the key manager)
  logic start_checker_q;
  logic checker_done, checker_good, checker_alert;
  rom_ctrl_compare #(
    .NumWords  (TopCount),
    .SkipCheck (SkipCheck)
  ) u_compare (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),
    .start_i      (start_checker_q),
    .done_o       (checker_done),
    .good_o       (checker_good),
    .digest_i     (digest_i),
    .exp_digest_i (exp_digest_i),
    .alert_o      (checker_alert)
  );

  // Main FSM
  //
  // There are the following logical states
  //
  //    ReadingLow:   We're reading the low part of ROM and passing it to KMAC
  //    ReadingHigh:  We're reading the high part of ROM and waiting for KMAC
  //    RomAhead:     We've finished reading the high part of ROM, but are still waiting for KMAC
  //    KmacAhead:    KMAC is done, but we're still reading the high part of ROM
  //    Checking:     We are comparing DIGEST and EXP_DIGEST and sending data to keymgr
  //    Done:         Terminal state
  //
  // The FSM is linear, except for the branch where reading the high part of ROM races with getting
  // the result back from KMAC.
  //
  //     digraph fsm {
  //       ReadingLow -> ReadingHigh;
  //       ReadingHigh -> RomAhead;
  //       ReadingHigh -> KmacAhead;
  //       RomAhead -> Checking;
  //       KmacAhead -> Checking;
  //       Checking -> Done;
  //       Done [peripheries=2];
  //     }
  //
  // Encoding generated with:
  // $ util/design/sparse-fsm-encode.py -d 3 -m 6 -n 6 -s 2 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (53.33%)
  //  4: ||||||||||||||| (40.00%)
  //  5: || (6.67%)
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 5
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 5
  //
  typedef enum logic [5:0] {
    ReadingLow  = 6'b111101,
    ReadingHigh = 6'b110110,
    RomAhead    = 6'b000011,
    KmacAhead   = 6'b101010,
    Checking    = 6'b010000,
    Done        = 6'b001100
  } state_e;

  logic [5:0]  state_q, state_d;
  logic        fsm_alert;

  prim_flop #(.Width(6), .ResetValue({ReadingLow}))
  u_state_regs (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .d_i    (state_d),
    .q_o    (state_q)
  );

  always_comb begin
    state_d = state_q;
    fsm_alert = 1'b0;

    unique case (state_q)
      ReadingLow: begin
        // Switch to ReadingHigh when counter_lnt is true and kmac_rom_rdy_i & kmac_rom_vld_o
        // (implying that the transaction went through)
        if (counter_lnt && kmac_rom_rdy_i && kmac_rom_vld_o) begin
          state_d = ReadingHigh;
        end
      end

      ReadingHigh: begin
        unique case ({kmac_done_i, counter_done})
          2'b01: state_d = RomAhead;
          2'b10: state_d = KmacAhead;
          2'b11: state_d = Checking;
          default: ; // No change
        endcase
      end

      RomAhead: begin
        if (kmac_done_i) state_d = Checking;
      end

      KmacAhead: begin
        if (counter_done) state_d = Checking;
      end

      Checking: begin
        if (checker_done) state_d = Done;
      end

      Done: begin
        // Final state
      end

      default: begin
        // Invalid state.
        fsm_alert = 1'b1;
      end
    endcase
  end

  // Route digest signals coming back from KMAC straight to the CSRs
  assign digest_o     = kmac_digest_i;
  assign digest_vld_o = kmac_done_i;

  // Snoop on ROM reads to populate EXP_DIGEST, one word at a time
  logic reading_top;
  logic [AW-1:0] rel_addr_wide;
  logic [TAW-1:0] rel_addr;

  assign reading_top = (state_q == ReadingHigh || state_q == KmacAhead) & ~counter_done;
  assign rel_addr_wide = counter_data_addr - TopStartAddr;
  assign rel_addr = rel_addr_wide[TAW-1:0];

  // The top bits of rel_addr_wide should always be zero if we're reading the top bits (because TAW
  // bits should be enough to encode the difference between counter_data_addr and TopStartAddr)
  `ASSERT(RelAddrWide_A, exp_digest_vld_o |-> ~|rel_addr_wide[AW-1:TAW])
  logic unused_top_rel_addr_wide;
  assign unused_top_rel_addr_wide = |rel_addr_wide[AW-1:TAW];

  assign exp_digest_o = rom_data_i;
  assign exp_digest_vld_o = reading_top;
  assign exp_digest_idx_o = rel_addr;

  // Pass the 'done' and 'good' signals directly from the checker
  assign pwrmgr_data_o = '{done: (state_q == Done), good: checker_good};

  // Pass the digest all-at-once to the keymgr
  assign keymgr_data_o = '{data: digest_i, valid: (state_q == Done)};

  // KMAC rom data interface
  //
  // This is almost handled by the counter, but we interpose ourselves once all but the top words
  // have been sent, squashing the extra data beats that come out as the counter reads through the
  // top words.
  assign counter_data_rdy = kmac_rom_rdy_i | (state_q != ReadingLow);
  assign kmac_rom_vld_o = counter_data_vld & (state_q == ReadingLow);
  assign kmac_rom_last_o = counter_lnt;

  // Start the checker when transitioning into the "Checking" state
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      start_checker_q <= 1'b0;
    end else begin
      start_checker_q <= (state_q != Checking) && (state_d == Checking);
    end
  end

  // We keep control of the ROM mux from reset until we're done
  assign rom_select_o = (state_q != Done);
  assign rom_addr_o = counter_read_addr;
  assign rom_req_o = counter_read_req;

  // TODO: There are lots more checks that we could do here (things like spotting vld signals that
  //       occur when we're in an FSM state that doesn't expect them)
  assign alert_o = fsm_alert | checker_alert;

endmodule
