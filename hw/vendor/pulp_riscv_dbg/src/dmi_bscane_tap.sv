// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

/// Replacement for the full JTAG tap with `BSCANE2` Xilinx elements which hook
/// into the FPGA native scan chain. Meant for FPGA boards which do not expose a
/// usable pin-header or a separate, programmable FTDI chip.

/// They replace the functionality of `dmi_jtag_tap.sv`. The file is
/// pin-compatible so that by selecting the appropriate file for the target it
/// can be transparently managed without relying on tick defines.
module dmi_jtag_tap #(
  // Ignored, defined by the FPGA model.
  parameter int unsigned IrLength = 5,
  // JTAG IDCODE Value
  parameter logic [31:0] IdcodeValue = 32'h00000001
  // xxxx             version
  // xxxxxxxxxxxxxxxx part number
  // xxxxxxxxxxx      manufacturer id
  // 1                required by standard
) (
  /// Unused. Here to maintain pin compatibility with `dmi_jtag_tap` so that it
  /// can be used as a drop-in replacement.
  input  logic        tck_i,
  input  logic        tms_i,
  input  logic        trst_ni,
  input  logic        td_i,
  output logic        td_o,
  output logic        tdo_oe_o,
  input  logic        testmode_i,

  output logic        tck_o,
  output logic        dmi_clear_o,
  output logic        update_o,
  output logic        capture_o,
  output logic        shift_o,
  output logic        tdi_o,
  output logic        dtmcs_select_o,
  input  logic        dtmcs_tdo_i,
  // we want to access DMI register
  output logic        dmi_select_o,
  input  logic        dmi_tdo_i
);

  BSCANE2 #(
    .JTAG_CHAIN (3)
  ) i_tap_dtmcs (
    .CAPTURE (capture_o),
    .DRCK (),
    .RESET (dmi_clear_o),
    .RUNTEST (),
    .SEL (dtmcs_select_o),
    .SHIFT (shift_o),
    .TCK (tck_o),
    .TDI (tdi_o),
    .TMS (),
    .TDO (dtmcs_tdo_i),
    .UPDATE (update_o)
  );

  /// DMI Register
  BSCANE2 #(
    .JTAG_CHAIN (4)
  ) i_tap_dmi (
    .CAPTURE (),
    .DRCK (),
    .RESET (),
    .RUNTEST (),
    .SEL (dmi_select_o),
    .SHIFT (),
    .TCK (),
    .TDI (),
    .TMS (),
    .TDO (dmi_tdo_i),
    .UPDATE ()
  );

endmodule
