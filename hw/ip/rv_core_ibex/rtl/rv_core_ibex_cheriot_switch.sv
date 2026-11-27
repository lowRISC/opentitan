// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Write-once ePMP/CHERIoT execution mode switch.
//
// The FSM resets unlocked, with the compare enable on and all other enables off, and advances on
// the first write to the lock register, which samples the mode selection and its complement;
// `unlocked_o` is high until then. It then raises its enables one per cycle (core, core shadow,
// memory subsystem, memory subsystem shadow) and checks the selection and its complement again in
// every staging cycle. For CHERIoT mode, it turns the compare enable off with the core's enable, as
// the enables of the lockstep copies differ while they are staged, and on again after the last one;
// for ePMP mode, no enable changes and the compare enable stays on. Each enable is held in its own
// flop, which only the step that changes it and the error handling write. Once locked it holds the
// selected mode until reset; an invalid lock/selection combination, a failed re-check or an invalid
// state encoding lands in the terminal error state. Every step into that state, also from an
// invalid state encoding, writes an invalid multi-bit value into all enables, so consumers fail
// closed, and the state raises `error_o` for the fatal alert.

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

  output logic unlocked_o,
  output logic error_o
);

  ////////////////
  // Switch FSM //
  ////////////////

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

  // Position of each enable in the enable flops, in the order the switch raises them
  typedef enum logic [2:0] {
    EnaCoreIdx,
    EnaCoreShadowIdx,
    EnaMemsysIdx,
    EnaMemsysShadowIdx,
    EnaCompareIdx,
    EnaLast
  } ena_idx_e;

  switch_state_e switch_state_d, switch_state_q;

  logic [EnaLast-1:0][MuBi4Width-1:0] ena_d, ena_q;

  always_comb begin : proc_switch_fsm

    // Default assignments. The enables hold unless a step or an error branch below writes them.
    switch_state_d = Error;
    unlocked_o     = 1'b0;
    error_o        = 1'b0;
    ena_d          = ena_q;

    unique case (switch_state_q)

      // We reset in unlocked
      Unlocked: begin
        unlocked_o = 1'b1;

        // The FSM advanced iff the lock register is written to
        if (lock_access_i) begin
          // If the proper lock value is written and we enable CHERIoT -> Enable state
          if (mubi4_test_true_strict(lock_i)  &&
              mubi4_test_true_strict(ena_i)   &&
              mubi4_test_false_strict(ena_ni)
             ) begin
            switch_state_d       = LockedCoreEna;
            ena_d[EnaCoreIdx]    = MuBi4True;
            ena_d[EnaCompareIdx] = MuBi4False;
          // If the proper lock value is written and we disable CHERIoT -> Disable state
          end else if (mubi4_test_true_strict(lock_i) &&
                       mubi4_test_false_strict(ena_i) &&
                       mubi4_test_true_strict(ena_ni)
                      ) begin
            // No enable changes in ePMP mode, so the compare enable stays on.
            switch_state_d    = LockedCoreDis;
            ena_d[EnaCoreIdx] = MuBi4False;
          // Otherwise we drop into the error state
          end else begin
            switch_state_d = Error;
            ena_d          = '0;
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
          switch_state_d          = LockedCoreShadowEna;
          ena_d[EnaCoreShadowIdx] = MuBi4True;
        end else begin
          switch_state_d = Error;
          ena_d          = '0;
        end
      end

      LockedCoreDis: begin
        if (mubi4_test_false_strict(ena_i) &&
            mubi4_test_true_strict(ena_ni)
           ) begin
          switch_state_d          = LockedCoreShadowDis;
          ena_d[EnaCoreShadowIdx] = MuBi4False;
        end else begin
          switch_state_d = Error;
          ena_d          = '0;
        end
      end

      LockedCoreShadowEna: begin
        if (mubi4_test_true_strict(ena_i) &&
            mubi4_test_false_strict(ena_ni)
           ) begin
          switch_state_d      = LockedMemSysEna;
          ena_d[EnaMemsysIdx] = MuBi4True;
        end else begin
          switch_state_d = Error;
          ena_d          = '0;
        end
      end

      LockedCoreShadowDis: begin
        if (mubi4_test_false_strict(ena_i) &&
            mubi4_test_true_strict(ena_ni)
           ) begin
          switch_state_d      = LockedMemSysDis;
          ena_d[EnaMemsysIdx] = MuBi4False;
        end else begin
          switch_state_d = Error;
          ena_d          = '0;
        end
      end

      LockedMemSysEna: begin
        if (mubi4_test_true_strict(ena_i) &&
            mubi4_test_false_strict(ena_ni)
           ) begin
          switch_state_d            = LockedMemSysShadowEna;
          ena_d[EnaMemsysShadowIdx] = MuBi4True;
        end else begin
          switch_state_d = Error;
          ena_d          = '0;
        end
      end

      LockedMemSysDis: begin
        if (mubi4_test_false_strict(ena_i) &&
            mubi4_test_true_strict(ena_ni)
           ) begin
          switch_state_d            = LockedMemSysShadowDis;
          ena_d[EnaMemsysShadowIdx] = MuBi4False;
        end else begin
          switch_state_d = Error;
          ena_d          = '0;
        end
      end

      LockedMemSysShadowEna: begin
        if (mubi4_test_true_strict(ena_i) &&
            mubi4_test_false_strict(ena_ni)
           ) begin
          switch_state_d       = LockedCompEna;
          ena_d[EnaCompareIdx] = MuBi4True;
        end else begin
          switch_state_d = Error;
          ena_d          = '0;
        end
      end

      LockedMemSysShadowDis: begin
        if (mubi4_test_false_strict(ena_i) &&
            mubi4_test_true_strict(ena_ni)
           ) begin
          switch_state_d = LockedCompDis;
        end else begin
          switch_state_d = Error;
          ena_d          = '0;
        end
      end

      LockedCompEna: begin
        // This is a terminal state
        switch_state_d = LockedCompEna;
      end

      LockedCompDis: begin
        // This is a terminal state
        switch_state_d = LockedCompDis;
      end

      Error: begin
        // This is a terminal state
        switch_state_d = Error;
        error_o        = 1'b1;
      end

      default: begin
        switch_state_d = Error;
        error_o        = 1'b1;
        ena_d          = '0;
      end
    endcase
  end

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, switch_state_d, switch_state_q, switch_state_e, Unlocked)

  //////////////////
  // Enable Flops //
  //////////////////

  // Each enable has its own flop, so a fault on the state register alone cannot set the enables of
  // the other mode. The anchor keeps all bits of each multi-bit value. The compare enable resets
  // on, as the enables of the lockstep copies stay equal until a lock to CHERIoT mode turns it off.
  // A step into the error state writes all zeros: invalid values for all enables, and for the
  // compare enable a value other than MuBi4False, which keeps the receivers' comparisons on so
  // they flag the invalid enables.
  for (genvar i = 0; i < EnaLast; i++) begin : gen_ena_flops
    prim_sec_anchor_flop #(
      .Width     (MuBi4Width),
      .ResetValue(MuBi4Width'(i == int'(EnaCompareIdx) ? MuBi4True : MuBi4False))
    ) u_prim_sec_anchor_flop_ena (
      .clk_i,
      .rst_ni,
      .d_i(ena_d[i]),
      .q_o(ena_q[i])
    );
  end

  assign ena_core_o          = mubi4_t'(ena_q[EnaCoreIdx]);
  assign ena_core_shadow_o   = mubi4_t'(ena_q[EnaCoreShadowIdx]);
  assign ena_memsys_o        = mubi4_t'(ena_q[EnaMemsysIdx]);
  assign ena_memsys_shadow_o = mubi4_t'(ena_q[EnaMemsysShadowIdx]);
  assign ena_compare_o       = mubi4_t'(ena_q[EnaCompareIdx]);

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_KNOWN(EnaCoreKnown_A,         ena_core_o)
  `ASSERT_KNOWN(EnaCoreShadowKnown_A,   ena_core_shadow_o)
  `ASSERT_KNOWN(EnaMemsysKnown_A,       ena_memsys_o)
  `ASSERT_KNOWN(EnaMemsysShadowKnown_A, ena_memsys_shadow_o)
  `ASSERT_KNOWN(EnaCompareKnown_A,      ena_compare_o)
  `ASSERT_KNOWN(UnlockedKnown_A,        unlocked_o)
  `ASSERT_KNOWN(ErrorKnown_A,           error_o)

  // The enable flops change only on a step of the FSM.
  `ASSERT(EnaChangeOnStep_A, ena_d != ena_q |-> switch_state_d != switch_state_q)

endmodule
