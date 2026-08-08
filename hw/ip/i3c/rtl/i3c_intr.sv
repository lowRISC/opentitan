// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Interrupt handling for a group of associated interrupts (HCI 6.14).

module i3c_intr #(
  // Number of interrupts implemented by this module instance.
  parameter int unsigned      Width    = 1,
  // Whether each interrupt is triggered by a rising edge rather than reflecting the current status.
  parameter logic [Width-1:0] EdgeTrig = 0
) (
  input               clk_i,
  input               rst_ni,

  // Interrupt event from internal logic.
  input   [Width-1:0] event_i,

  // Interrupt enable.
  input   [Width-1:0] status_en_i,
  // Set/clear interrupt status bit in HCI register.
  output  [Width-1:0] status_de_o,
  // New state of interrupt status bit in HCI register.
  output  [Width-1:0] status_d_o,
  // Interrupt force signal from HCI register.
  input   [Width-1:0] force_i,
  // Interrupt status bit from configuration registers.
  input   [Width-1:0] status_i,
  // Interrupt signal enable from HCI configuration.
  input   [Width-1:0] signal_en_i,

  // Interrupt signal to system.
  output logic        intr_o
);

  // The HCI defines four groups of interrupts:
  //
  // - Host Controller.
  // - PIO.
  // - Standby Controller.
  // - Ring Header (not required in this IP because DMA is not implemented).
  //
  // The OpenTitan TTI also uses the same mechanism for Target-side interrupts.
  //
  // Each has an associated set of registers:
  // - _INTR_STATUS        - Indicates the current interrupt status and permits interrupt clearing.
  // - _INTR_STATUS_ENABLE - Enables/disables the setting of interrupt state by controller events.
  // - _INTR_SIGNAL_ENABLE - Enables/disables the generation of interrupt signals from their status.
  // - _INTR_FORCE         - Software-controlled forcing of the interrupt status for diagnostic use.
  //
  // Notes:
  // - interrupt status bit may be cleared by software writing a '1' or by clearing the Queue/FIFO
  //   condition that caused the underlying interrupt condition to trigger.
  // - interrupts related to exceptional events such as error conditions shall not, of course,
  //   disappear when a recoverable error condition has passed.

  // Edge-triggered interrupts only ever set the Interrupt Status bit, and it will be cleared by
  // software at a later time.
  //
  // Level-sensitive interrupts need both to set and to clear the Interrupt status bit, although
  // note that clearing by software is still permitted for HCI-style registers.
  logic [Width-1:0] set_status;

  // Interrupt status bits are set only when enabled, and may be set by:
  // - the occurrence of enabled events, or
  // - software forcing of the status bit for diagnostic/testing purposes.
  assign set_status = status_en_i & (force_i | (event_i & ~status_i));

  // Interrupt clearing is performed only for level-sensitive interrupts.
  logic [Width-1:0] clr_status;
  assign clr_status = (status_i & ~event_i) & ~EdgeTrig;

  // Drive out OpenTitan-style 'data enable' and 'data' values.
  assign status_de_o = set_status | clr_status;
  assign status_d_o  = set_status;  // Reporting of new interrupts takes precedence.

  // No need to register the interrupt output here because this is not the final stage for
  // the OpenTitan implementation; there is a `prim_intr_hw` instance with a flop stage.
  assign intr_o = |(signal_en_i & status_i);

endmodule
