// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Write-once ePMP/CHERIoT execution mode switch.
//
// The FSM resets unlocked and advances on the first write to the lock register. Once locked it
// reports the selected mode until reset; an invalid lock/enable combination or an invalid state
// encoding lands in the terminal error state, which reports ePMP mode.

`include "prim_assert.sv"

module cheriot_switch
  import prim_mubi_pkg::*;
(
  input  logic clk_i,
  input  logic rst_ni,

  input  mubi4_t ena_i,
  input  mubi4_t lock_i,
  input  logic   lock_access_i,
  output mubi4_t ena_o,

  output logic error_o
);

  // Encoding generated at commit feacd8763c using Python 3.12.13 with:
  // $ ./util/design/sparse-fsm-encode.py --language=sv \
  //     --seed 492361 --distance 4 --states 4 --bits 6
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: |||||||||||||||||||| (100.00%)
  //  5: --
  //  6: --
  //
  // Minimum Hamming distance: 4
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 5
  //
  localparam int SwitchStateWidth = 6;
  typedef enum logic [SwitchStateWidth-1:0] {
    Unlocked  = 6'b010110,
    LockedEna = 6'b100101,
    LockedDis = 6'b111011,
    Error     = 6'b001000
  } switch_state_e;

  switch_state_e switch_state_d, switch_state_q;

  always_comb begin : proc_switch_fsm

    // Default assignments
    switch_state_d = Error;
    error_o        = 1'b0;
    ena_o          = MuBi4False;

    unique case (switch_state_q)

      // We reset in unlocked
      Unlocked: begin

        // The FSM advanced iff the lock register is written to
        if (lock_access_i) begin
          // If the proper lock value is written and we enable CHERIoT -> Enable state
          if (mubi4_test_true_strict(lock_i) && mubi4_test_true_strict(ena_i)) begin
            switch_state_d = LockedEna;
          // If the proper lock value is written and we disable CHERIoT -> Disable state
          end else if (mubi4_test_true_strict(lock_i) && mubi4_test_false_strict(ena_i)) begin
            switch_state_d = LockedDis;
          // Otherwise we drop into the error state
          end else begin
            switch_state_d = Error;
          end

        // The lock register is not written to, we remain unlocked
        end else begin
          switch_state_d = Unlocked;
        end
      end

      LockedEna: begin
        switch_state_d = LockedEna;
        ena_o          = MuBi4True;
      end

      LockedDis: begin
        switch_state_d = LockedDis;
        ena_o          = MuBi4False;
      end

      // Enable set to MuBi4False is the proper state on error, this means we remain in ePMP mode
      // which is secure at the stage of the switch.
      Error: begin
        switch_state_d = Error;
        ena_o          = MuBi4False;
        error_o        = 1'b1;
      end

      default: begin
        switch_state_d = Error;
        ena_o          = MuBi4False;
        error_o        = 1'b1;
      end
    endcase
  end

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, switch_state_d, switch_state_q, switch_state_e, Unlocked)

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_KNOWN(EnaKnown_A,   ena_o)
  `ASSERT_KNOWN(ErrorKnown_A, error_o)

endmodule
