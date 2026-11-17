// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Write-once ePMP/CHERIoT execution mode switch.
//
// The FSM resets unlocked and advances on the first write to the lock register, which samples the
// mode selection and its complement. It then raises its enables one per cycle (core, core shadow,
// memory subsystem, memory subsystem shadow, compare) and checks the selection and its complement
// again in every staging cycle. Once locked it holds the selected mode until reset; an invalid
// lock/enable combination, a failed re-check or an invalid state encoding lands in the terminal
// error state. That state drives an invalid multi-bit value on all enables, so consumers fail
// closed, and raises `error_o` for the fatal alert.

`include "prim_assert.sv"

module rv_core_ibex_cheriot_switch
  import prim_mubi_pkg::*;
(
  input  logic clk_i,
  input  logic rst_ni,

  input  mubi4_t ena_i,
  input  mubi4_t ena_ni,
  input  mubi4_t lock_i,
  input  logic   lock_access_i,
  output mubi4_t ena_core_o,
  output mubi4_t ena_core_shadow_o,
  output mubi4_t ena_memsys_o,
  output mubi4_t ena_memsys_shadow_o,
  output mubi4_t ena_compare_o,

  output logic error_o
);

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py --language=sv \
  //     --seed 492361 --distance 4 --states 12 --bits 12
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: |||||||| (12.12%)
  //  5: |||||||||||| (18.18%)
  //  6: |||||||||||||||||||| (28.79%)
  //  7: ||||||||||||| (19.70%)
  //  8: ||||||||| (13.64%)
  //  9: || (3.03%)
  // 10: ||| (4.55%)
  // 11: --
  // 12: --
  //
  // Minimum Hamming distance: 4
  // Maximum Hamming distance: 10
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 9
  //
  localparam int SwitchStateWidth = 12;
  typedef enum logic [SwitchStateWidth-1:0] {
    Unlocked              = 12'b010110010100,
    LockedCoreEna         = 12'b011000010101,
    LockedCoreDis         = 12'b100111010111,
    LockedCoreShadowEna   = 12'b111011110110,
    LockedCoreShadowDis   = 12'b011011101011,
    LockedMemSysEna       = 12'b000010011000,
    LockedMemSysDis       = 12'b100100011110,
    LockedMemSysShadowEna = 12'b110110101010,
    LockedMemSysShadowDis = 12'b101000010011,
    LockedCompEna         = 12'b010011100100,
    LockedCompDis         = 12'b001100000111,
    Error                 = 12'b111101000000
  } switch_state_e;

  switch_state_e switch_state_d, switch_state_q;

  always_comb begin : proc_switch_fsm

    // Default assignments
    switch_state_d      = Error;
    error_o             = 1'b0;
    ena_core_o          = MuBi4False;
    ena_core_shadow_o   = MuBi4False;
    ena_memsys_o        = MuBi4False;
    ena_memsys_shadow_o = MuBi4False;
    ena_compare_o       = MuBi4False;

    unique case (switch_state_q)

      // We reset in unlocked
      Unlocked: begin

        // The FSM advanced iff the lock register is written to
        if (lock_access_i) begin
          // If the proper lock value is written and we enable CHERIoT -> Enable state
          if (mubi4_test_true_strict(lock_i)  &&
              mubi4_test_true_strict(ena_i)   &&
              mubi4_test_false_strict(ena_ni)
             ) begin
            switch_state_d = LockedCoreEna;
          // If the proper lock value is written and we disable CHERIoT -> Disable state
          end else if (mubi4_test_true_strict(lock_i) &&
                       mubi4_test_false_strict(ena_i) &&
                       mubi4_test_true_strict(ena_ni)
                      ) begin
            switch_state_d = LockedCoreDis;
          // Otherwise we drop into the error state
          end else begin
            switch_state_d = Error;
          end

        // The lock register is not written to, we remain unlocked
        end else begin
          switch_state_d = Unlocked;
        end
      end

      LockedCoreEna: begin
        if (mubi4_test_true_strict(ena_i) &&
            mubi4_test_false_strict(ena_ni)
           ) begin
          switch_state_d = LockedCoreShadowEna;
        end else begin
          switch_state_d = Error;
        end
        ena_core_o = MuBi4True;
      end

      LockedCoreDis: begin
        if (mubi4_test_false_strict(ena_i) &&
            mubi4_test_true_strict(ena_ni)
           ) begin
          switch_state_d = LockedCoreShadowDis;
        end else begin
          switch_state_d = Error;
        end
        ena_core_o = MuBi4False;
      end

      LockedCoreShadowEna: begin
        if (mubi4_test_true_strict(ena_i) &&
            mubi4_test_false_strict(ena_ni)
           ) begin
          switch_state_d = LockedMemSysEna;
        end else begin
          switch_state_d = Error;
        end
        ena_core_o        = MuBi4True;
        ena_core_shadow_o = MuBi4True;
      end

      LockedCoreShadowDis: begin
        if (mubi4_test_false_strict(ena_i) &&
            mubi4_test_true_strict(ena_ni)
           ) begin
          switch_state_d = LockedMemSysDis;
        end else begin
          switch_state_d = Error;
        end
        ena_core_o        = MuBi4False;
        ena_core_shadow_o = MuBi4False;
      end

      LockedMemSysEna: begin
        if (mubi4_test_true_strict(ena_i) &&
            mubi4_test_false_strict(ena_ni)
           ) begin
          switch_state_d = LockedMemSysShadowEna;
        end else begin
          switch_state_d = Error;
        end
        ena_core_o        = MuBi4True;
        ena_core_shadow_o = MuBi4True;
        ena_memsys_o      = MuBi4True;
      end

      LockedMemSysDis: begin
        if (mubi4_test_false_strict(ena_i) &&
            mubi4_test_true_strict(ena_ni)
           ) begin
          switch_state_d = LockedMemSysShadowDis;
        end else begin
          switch_state_d = Error;
        end
        ena_core_o        = MuBi4False;
        ena_core_shadow_o = MuBi4False;
        ena_memsys_o      = MuBi4False;
      end

      LockedMemSysShadowEna: begin
        if (mubi4_test_true_strict(ena_i) &&
            mubi4_test_false_strict(ena_ni)
           ) begin
          switch_state_d = LockedCompEna;
        end else begin
          switch_state_d = Error;
        end
        ena_core_o          = MuBi4True;
        ena_core_shadow_o   = MuBi4True;
        ena_memsys_o        = MuBi4True;
        ena_memsys_shadow_o = MuBi4True;
      end

      LockedMemSysShadowDis: begin
        if (mubi4_test_false_strict(ena_i) &&
            mubi4_test_true_strict(ena_ni)
           ) begin
          switch_state_d = LockedCompDis;
        end else begin
          switch_state_d = Error;
        end
        ena_core_o          = MuBi4False;
        ena_core_shadow_o   = MuBi4False;
        ena_memsys_o        = MuBi4False;
        ena_memsys_shadow_o = MuBi4False;
      end

      LockedCompEna: begin
        // This is a terminal state
        switch_state_d      = LockedCompEna;
        ena_core_o          = MuBi4True;
        ena_core_shadow_o   = MuBi4True;
        ena_memsys_o        = MuBi4True;
        ena_memsys_shadow_o = MuBi4True;
        ena_compare_o       = MuBi4True;
      end

      LockedCompDis: begin
        // This is a terminal state
        switch_state_d      = LockedCompDis;
        ena_core_o          = MuBi4False;
        ena_core_shadow_o   = MuBi4False;
        ena_memsys_o        = MuBi4False;
        ena_memsys_shadow_o = MuBi4False;
        ena_compare_o       = MuBi4True;
      end

      Error: begin
        // This is a terminal state
        switch_state_d      = Error;
        ena_core_o          = mubi4_t'(4'h0);
        ena_core_shadow_o   = mubi4_t'(4'h0);
        ena_memsys_o        = mubi4_t'(4'h0);
        ena_memsys_shadow_o = mubi4_t'(4'h0);
        ena_compare_o       = mubi4_t'(4'h0);
        error_o             = 1'b1;
      end

      default: begin
        switch_state_d      = Error;
        ena_core_o          = mubi4_t'(4'h0);
        ena_core_shadow_o   = mubi4_t'(4'h0);
        ena_memsys_o        = mubi4_t'(4'h0);
        ena_memsys_shadow_o = mubi4_t'(4'h0);
        ena_compare_o       = mubi4_t'(4'h0);
        error_o             = 1'b1;
      end
    endcase
  end

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, switch_state_d, switch_state_q, switch_state_e, Unlocked)

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_KNOWN(EnaCoreKnown_A,         ena_core_o)
  `ASSERT_KNOWN(EnaCoreShadowKnown_A,   ena_core_shadow_o)
  `ASSERT_KNOWN(EnaMemsysKnown_A,       ena_memsys_o)
  `ASSERT_KNOWN(EnaMemsysShadowKnown_A, ena_memsys_shadow_o)
  `ASSERT_KNOWN(EnaCompareKnown_A,      ena_compare_o)
  `ASSERT_KNOWN(ErrorKnown_A,           error_o)

endmodule
