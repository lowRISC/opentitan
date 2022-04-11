// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// The ROM checker FSM module
//

`include "prim_assert.sv"

module rom_ctrl_fsm
  import prim_mubi_pkg::mubi4_t;
  import prim_util_pkg::vbits;
  import rom_ctrl_pkg::*;
#(
  parameter int RomDepth = 16,
  parameter int TopCount = 8
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
  output pwrmgr_data_t pwrmgr_data_o,
  output keymgr_data_t keymgr_data_o,

  // To KMAC (ROM data)
  input logic                        kmac_rom_rdy_i,
  output logic                       kmac_rom_vld_o,
  output logic                       kmac_rom_last_o,

  // To KMAC (digest data)
  input logic                        kmac_done_i,
  input logic [TopCount*32-1:0]      kmac_digest_i,
  input logic                        kmac_err_i,

  // To ROM mux
  output mubi4_t                     rom_select_bus_o,
  output logic [vbits(RomDepth)-1:0] rom_addr_o,
  output logic                       rom_req_o,

  // Raw bits from ROM
  input logic [31:0]                 rom_data_i,

  // To alert system
  output logic                       alert_o
);

  import prim_mubi_pkg::mubi4_test_true_loose;
  import prim_mubi_pkg::MuBi4False, prim_mubi_pkg::MuBi4True;

  localparam int AW = vbits(RomDepth);
  localparam int TAW = vbits(TopCount);

  localparam int unsigned TopStartAddrInt = RomDepth - TopCount;
  localparam bit [AW-1:0] TopStartAddr    = TopStartAddrInt[AW-1:0];

  // The counter / address generator
  logic          counter_done;
  logic [AW-1:0] counter_read_addr;
  logic          counter_read_req;
  logic [AW-1:0] counter_data_addr;
  logic          counter_data_rdy;
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
    .data_last_nontop_o (counter_lnt)
  );

  // The compare block (responsible for comparing CSR data and forwarding it to the key manager)
  logic   start_checker_q;
  logic   checker_done, checker_alert;
  mubi4_t checker_good;
  rom_ctrl_compare #(
    .NumWords  (TopCount)
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
  //    Invalid:      Terminal and invalid state (only reachable by a glitch)
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
  // SEC_CM: FSM.SPARSE
  // SEC_CM: INTERSIG.MUBI

  fsm_state_e state_d, state_q;
  logic       fsm_alert;

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, fsm_state_e, ReadingLow)

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
          2'b10: state_d = kmac_err_i ? Invalid : KmacAhead;
          2'b11: state_d = kmac_err_i ? Invalid : Checking;
          default: ; // No change
        endcase
      end

      RomAhead: begin
        if (kmac_done_i) state_d = kmac_err_i ? Invalid : Checking;
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
        // An invalid state (includes the explicit Invalid state)
        fsm_alert = 1'b1;
        state_d = Invalid;
      end
    endcase

    // Consistency checks for done signals.
    //
    // If checker_done is high in a state other than Checking or Done then something has gone wrong
    // and we ran the check early. Similarly, counter_done should only be high after we've left
    // ReadingLow. Finally, kmac_done_i should only be high in ReadingHigh or RomAhead. If any of
    // these consistency requirements don't hold, jump to the Invalid state. This will also raise an
    // alert on the following cycle.
    //
    // SEC_CM: CHECKER.CTRL_FLOW.CONSISTENCY
    if ((checker_done && !(state_q inside {Checking, Done})) ||
        (counter_done && state_q == ReadingLow) ||
        (kmac_done_i && !(state_q inside {ReadingHigh, RomAhead}))) begin
      state_d = Invalid;
    end

    // Jump to an invalid state if sending out an alert for any other reason
    //
    // SEC_CM: CHECKER.FSM.LOCAL_ESC
    if (alert_o) begin
      state_d = Invalid;
    end
  end

  // The in_state_done signal is supposed to be true iff we're in FSM state Done. Grabbing just the
  // bottom 4 bits of state_q is equivalent to "mubi4_bool_to_mubi(state_q == Done)" except that it
  // doesn't have a 1-bit signal on the way.
  logic [9:0] state_q_bits;
  logic       unused_state_q_top_bits;
  assign state_q_bits = {state_q};
  assign unused_state_q_top_bits = ^state_q_bits[9:4];

  mubi4_t in_state_done;
  assign in_state_done = mubi4_t'(state_q_bits[3:0]);

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

  // The 'done' signal for pwrmgr is asserted once we get into the Done state. The 'good' signal
  // compes directly from the checker.
  assign pwrmgr_data_o = '{done: in_state_done, good: checker_good};

  // Pass the digest all-at-once to the keymgr. The loose check means that glitches will add
  // spurious edges to the valid signal that can be caught at the other end.
  assign keymgr_data_o = '{data: digest_i, valid: mubi4_test_true_loose(in_state_done)};

  // KMAC rom data interface
  logic kmac_rom_vld_d, kmac_rom_vld_q;
  always_comb begin
    // There will be valid data to pass to KMAC on each cycle after a counter request has gone out
    // when we were in state ReadingLow. That data goes out (causing us to drop the valid signal) if
    // KMAC was ready. Note that this formulation allows kmac_rom_vld_q to be high even if we're not
    // in the ReadingLow state: if something goes wrong and we get faulted into Invalid then we'll
    // still correctly send the end of the KMAC transaction.
    kmac_rom_vld_d = kmac_rom_vld_q;
    if (kmac_rom_rdy_i) begin
      kmac_rom_vld_d = 0;
    end
    if (counter_read_req && state_q == ReadingLow && !counter_lnt) begin
      kmac_rom_vld_d = 1;
    end
  end
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      kmac_rom_vld_q <= 0;
    end else begin
      kmac_rom_vld_q <= kmac_rom_vld_d;
    end
  end

  assign counter_data_rdy = kmac_rom_rdy_i | (state_q inside {ReadingHigh, KmacAhead});
  assign kmac_rom_vld_o = kmac_rom_vld_q;
  assign kmac_rom_last_o = counter_lnt;

  // The "last" flag is signalled when we're reading the last word in the first part of the ROM. As
  // a quick consistency check, this should only happen when the "valid" flag is also high.
  `ASSERT(LastImpliesValid_A, kmac_rom_last_o |-> kmac_rom_vld_o)

  // Start the checker when transitioning into the "Checking" state
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      start_checker_q <= 1'b0;
    end else begin
      start_checker_q <= (state_q != Checking) && (state_d == Checking);
    end
  end

  // The counter is supposed to run from zero up to the top of memory and then tell us that it's
  // done with the counter_done signal. We would like to be sure that no-one can fiddle with the
  // counter address once the hash has been computed (if they could subvert the mux as well, this
  // would allow them to generate a useful wrong address for a fetch). Fortunately, doing so would
  // cause the counter_done signal to drop again and we *know* that it should stay high when our FSM
  // is in the Done state.
  //
  // SEC_CM: CHECKER.CTR.CONSISTENCY
  logic unexpected_counter_change;
  assign unexpected_counter_change = mubi4_test_true_loose(in_state_done) & !counter_done;

  // We keep control of the ROM mux from reset until we're done.
  assign rom_select_bus_o = in_state_done;

  assign rom_addr_o = counter_read_addr;
  assign rom_req_o = counter_read_req;

  assign alert_o = fsm_alert | checker_alert | unexpected_counter_change;

endmodule
