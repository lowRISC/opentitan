// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// The ROM checker FSM module
//
// This is an FSM that controls the interaction with KMAC to calculate a digest from the ROM
// contents.
//
// The digest_i and exp_digest_i ports are wide signals for the computed digest from KMAC and the
// expected digest (which has been read from the top of ROM). Both digests are stored in CSR
// registers.
//
// The digest_o port gives the computed digest from KMAC and the value is valid if digest_vld_o is
// true. This value will be written into the DIGEST register.
//
// Similarly, the exp_digest_o port gives a 32-bit word of the expected digest with index
// exp_digest_idx_o. The values are valid if exp_digest_vld_o is true.
//
// The pwrmgr_data_o port gives the data that should be sent to pwrmgr. This consists of a "done"
// field (showing that the digest has been computed and checked against the expected value) and a
// "good" field (which shows that the two digests matched).
//
// The keymgr_data_o port gives the data that should be sent to keymgr. This is the computed hash
// (from digest_i) with a valid signal to show the data field is valid.
//
// The kmac_rom_* ports are sending ROM data to KMAC. The kmac_rom_rdy_i / kmac_rom_vld_o signals
// give a ready/valid interface to control the handshake that passes ROM data to KMAC to be hashed.
// The kmac_rom_last_o signal is high when the word being offered is the last word of the input.
//
// The other kmac_* ports are for the digest coming back from KMAC. The kmac_digest_i signal is the
// computed digest, which is valid if kmac_done_i is true unless kmac_err_i is true, in which case
// the KMAC block encountered an error when computing a digest.
//
// Immediately after reset, the FSM is in control of ROM requests. The rom_select_bus_o signal
// becomes MuBi4True when we have read the entire contents and the mux should instead give access to
// the bus. Until that happens, it should service the requests the FSM makes with rom_addr_o.
//
// Raw words from ROM appear in rom_data_i (to be incorporated into the expected digest).
//
// The alert_o signal goes high if an error has been seen, which should cause a fatal alert.

`include "prim_assert.sv"

module rom_ctrl_fsm
  import prim_mubi_pkg::mubi4_t;
  import prim_util_pkg::vbits;
  import rom_ctrl_pkg::*;
#(
  parameter int           RomDepth = 16,
  parameter int           TopCount = 8,

  // The width of data words stored in the ROM (along with extra integrity bits)
  parameter int unsigned  DataWidth = 39,

  // If this parameter is set, the ROM responds in two cycles (instead of one). The FSM needs to
  // track this because it sends ROM read addresses through rom_addr_o and needs to know which
  // response (in rom_data_i) corresponds to which address.
  parameter bit           TwoCycleRom = 1'b0,

  localparam int unsigned AW = vbits(RomDepth), // derived parameter
  localparam int unsigned TAW = vbits(TopCount) // derived parameter
) (
  input logic                    clk_i,
  input logic                    rst_ni,

  // CSR inputs for DIGEST and EXP_DIGEST. To make the indexing look nicer, these are ordered so
  // that DIGEST_0 is the bottom 32 bits (they get reversed while we're shuffling around the wires
  // in rom_ctrl).
  input logic [TopCount*32-1:0]  digest_i,
  input logic [TopCount*32-1:0]  exp_digest_i,

  // CSR outputs for DIGEST and EXP_DIGEST. Ordered with word 0 as LSB.
  output logic [TopCount*32-1:0] digest_o,
  output logic                   digest_vld_o,
  output logic [31:0]            exp_digest_o,
  output logic                   exp_digest_vld_o,
  output logic [TAW-1:0]         exp_digest_idx_o,

  // To power manager and key manager
  output pwrmgr_data_t           pwrmgr_data_o,
  output keymgr_data_t           keymgr_data_o,

  // To KMAC (ROM data)
  input logic                    kmac_rom_rdy_i,
  output logic                   kmac_rom_vld_o,
  output logic                   kmac_rom_last_o,
  output logic [DataWidth-1:0]   kmac_rom_data_o,

  // From KMAC (digest data)
  input logic                    kmac_done_i,
  input logic [TopCount*32-1:0]  kmac_digest_i,
  input logic                    kmac_err_i,

  // To ROM mux
  output mubi4_t                 rom_select_bus_o,
  output logic [AW-1:0]          rom_addr_o,

  // Raw bits from ROM
  input logic [DataWidth-1:0]    rom_data_i,

  // To alert system
  output logic                   alert_o
);

  import prim_mubi_pkg::mubi4_test_true_loose;
  import prim_mubi_pkg::MuBi4False, prim_mubi_pkg::MuBi4True;

  localparam int unsigned TopStartAddrInt = RomDepth - TopCount;
  localparam bit [AW-1:0] TopStartAddr    = TopStartAddrInt[AW-1:0];
  localparam int unsigned RomLatency = TwoCycleRom ? 2 : 1;

  // The counter / address generator
  logic          counter_done;
  logic [AW-1:0] counter_read_addr;
  logic          counter_read_data_top;
  logic          counter_data_rdy;
  rom_ctrl_counter #(
    .RomDepth (RomDepth),
    .RomTopCount (TopCount)
  ) u_counter (
    .clk_i              (clk_i),
    .rst_ni             (rst_ni),
    .done_o             (counter_done),
    .read_addr_o        (counter_read_addr),
    .read_last_data_o   (counter_read_data_top),
    .data_rdy_i         (counter_data_rdy)
  );

  logic [RomLatency-1:0] rdts_q, rdts_d;
  logic                  resp_data_top;
  logic                  unused_rdt;

  assign {unused_rdt, rdts_d} = {rdts_q, counter_read_data_top};
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rdts_q <= '0;
    end else begin
      rdts_q <= rdts_d;
    end
  end
  assign resp_data_top = rdts_q[RomLatency - 1];

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

  // We read items from ROM into a FIFO. To make sure we don't run out of space, we keep a counter
  // of the number of "slots left in the FIFO", decrementing it when we send a request to ROM and
  // incrementing it when a value gets popped out of the FIFO. To allow maximum bandwidth, the FIFO
  // is RomLatency items long: if one request is sent each cycle, we can be in a situation where
  // RomLatency requests are in flight and one is in the FIFO.
  //
  // Note that the counter needs to be able to represent the size of the FIFO (for when there are no
  // requests in flight).
  localparam int unsigned FifoLen = RomLatency + 1;
  localparam int unsigned RLW = vbits(FifoLen + 1);
  logic [RLW-1:0]         free_slots_d, free_slots_q;
  logic                   low_read_start, low_read_end;

  always_comb begin
    state_d = state_q;
    fsm_alert = 1'b0;

    unique case (state_q)
      ReadingLow: begin
        // Switch to ReadingHigh when counter_read_data_top & kmac_rom_rdy_i is true (implying that
        // the last word of the low section has been requested and the counter will switch to the
        // high section next cycle).
        if (counter_read_data_top && low_read_start) begin
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

  // Check that the FSM is linear and does not contain any loops
  `ASSERT_FPV_LINEAR_FSM(SecCmCFILinear_A, state_q, fsm_state_e)

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

  // Snoop on ROM reads to populate EXP_DIGEST, one word at a time. The address that is being
  // requested of the ROM is in counter_read_addr, which is at index read_rel_addr_wide in the
  // digest (once we are reading it). To allow a positive delay for ROM response (1 or 2 cycles), we
  // make a shift register, then store the address of the rom_data_i response into data_rel_addr.
  logic [AW-1:0]                  read_rel_addr_wide;
  logic [RomLatency-1:0][TAW-1:0] rel_addrs_q, rel_addrs_d;
  logic [TAW-1:0]                 unused_rel_addr;
  logic [TAW-1:0]                 data_rel_addr;
  logic [AW-TAW-1:0]              unused_rel_addr_wide;

  assign read_rel_addr_wide = counter_read_addr - TopStartAddr;
  assign {unused_rel_addr, rel_addrs_d} = {rel_addrs_q, read_rel_addr_wide[TAW-1:0]};
  assign unused_rel_addr_wide = read_rel_addr_wide[AW-1:TAW];

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rel_addrs_q <= '0;
    end else begin
      rel_addrs_q <= rel_addrs_d;
    end
  end

  assign data_rel_addr = rel_addrs_q[RomLatency-1];

  // The reading_top signal means that we are currently receiving data that we have read from the
  // top of ROM. This gets delayed by a short time (depending on RomLatency) to give just_read_top
  // (the data we are receiving now is from the top of ROM).
  logic                  reading_top;
  logic [RomLatency-1:0] reading_tops_d, reading_tops_q;
  logic                  unused_reading_top;
  logic                  just_read_top;

  assign reading_top = (state_q == ReadingHigh || state_q == KmacAhead) & ~counter_done;
  assign {unused_reading_top, reading_tops_d} = {reading_tops_q, reading_top};

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      reading_tops_q <= '0;
    end else begin
      reading_tops_q <= reading_tops_d;
    end
  end

  assign just_read_top = reading_tops_q[RomLatency-1];

  assign exp_digest_o = rom_data_i[31:0];
  assign exp_digest_vld_o = just_read_top;
  assign exp_digest_idx_o = data_rel_addr;

  // The 'done' signal for pwrmgr is asserted once we get into the Done state. The 'good' signal
  // comes directly from the checker.
  assign pwrmgr_data_o = '{done: in_state_done, good: checker_good};

  // Pass the digest all-at-once to the keymgr. The loose check means that glitches will add
  // spurious edges to the valid signal that can be caught at the other end.
  assign keymgr_data_o = '{data: digest_i, valid: mubi4_test_true_loose(in_state_done)};

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      free_slots_q <= FifoLen;
    end else begin
      free_slots_q <= free_slots_d;
    end
  end

  assign low_read_start = (free_slots_q != 0) && (state_q == ReadingLow);
  assign low_read_end = (free_slots_q < FifoLen) && kmac_rom_rdy_i;

  always_comb begin
    free_slots_d = free_slots_q;
    if (low_read_start) begin
      free_slots_d -= 1;
    end
    if (low_read_end) begin
      free_slots_d += 1;
    end
  end

  // As well as the counter above, we keep a queue in a shift register that can tell us whether a
  // ROM request is coming back from ROM and being stored into the FIFO. Note that this *might* flow
  // straight through the FIFO (because the Pass parameter is true).
  logic [RomLatency-1:0] store_response_d, store_response_q;
  logic                  unused_store_response;
  assign {unused_store_response, store_response_d} = {store_response_q, low_read_start};
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      store_response_q <= '0;
    end else begin
      store_response_q <= store_response_d;
    end
  end

  prim_fifo_sync #(
    .Width(1 + DataWidth),
    .Pass(1'b1),
    .Depth(FifoLen),
    .OutputZeroIfEmpty(1'b0),
    .NeverClears(1'b1),
    .Secure(0)
  ) u_kmac_fifo (
    .clk_i,
    .rst_ni,
    .clr_i    (1'b0),
    .wvalid_i (store_response_q[RomLatency-1]),
    .wready_o (),
    .wdata_i  ({resp_data_top, rom_data_i}),
    .rvalid_o (kmac_rom_vld_o),
    .rready_i (kmac_rom_rdy_i),
    .rdata_o  ({kmac_rom_last_o, kmac_rom_data_o}),
    .full_o   (),
    .depth_o  (),
    .err_o    ()
  );

  // The timing is carefully set up to ensure we don't request values if there's not space to store
  // them when they come back. As such, we don't look at u_kmac_fifo.wready_o. This assertion checks
  // that we're not dropping anything.
  `ASSERT(NoOverflow_A, u_kmac_fifo.wvalid_i |-> u_kmac_fifo.wready_o)

  // We tell the counter that we are consuming the current value if we are currently reading the
  // high part of ROM (because there is no back pressure for that information). For the low part of
  // ROM, we use the ready signal from KMAC. Note that kmac_rom_rdy_i might drop before the value
  // comes back from ROM, and u_kmac_fifo is used to catch it.
  assign counter_data_rdy = (free_slots_q > 0) | (state_q inside {ReadingHigh, KmacAhead});

  // The "last" flag is signalled when we're presenting the last word of the first part of the ROM.
  // As a quick consistency check, this should only be true when the "valid" flag is also high.
  `ASSERT(LastImpliesValid_A, kmac_rom_last_o |-> kmac_rom_vld_o,
          clk_i, !rst_ni || (state_q == Invalid))

  // Start the checker when transitioning into the "Checking" state. Note that the top word of the
  // expected digest might actually arrive on this cycle (KMAC responded quickly and if TwoCycleRom
  // is true), but that doesn't matter because we'll check the other words of the expected digest
  // first anyway.
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

  assign alert_o = fsm_alert | checker_alert | unexpected_counter_change;

endmodule
