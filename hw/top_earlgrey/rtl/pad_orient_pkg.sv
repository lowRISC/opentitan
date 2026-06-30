// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Open-source pad orientation definitions.
// This is only relevant for the ASIC target.

package pad_orient_pkg;

  import prim_pad_wrapper_pkg::*;

  parameter pad_orient_e DioPadAstMiscPadOrient        = OrientH;
  parameter pad_orient_e DioPadPorNPadOrient           = OrientH;
  parameter pad_orient_e DioPadSpiHostD0PadOrient      = OrientH;
  parameter pad_orient_e DioPadSpiHostD1PadOrient      = OrientH;
  parameter pad_orient_e DioPadSpiHostD2PadOrient      = OrientH;
  parameter pad_orient_e DioPadSpiHostD3PadOrient      = OrientH;
  parameter pad_orient_e DioPadSpiHostClkPadOrient     = OrientH;
  parameter pad_orient_e DioPadSpiHostCsLPadOrient     = OrientH;
  parameter pad_orient_e DioPadSpiDevD0PadOrient       = OrientH;
  parameter pad_orient_e DioPadSpiDevD1PadOrient       = OrientH;
  parameter pad_orient_e DioPadSpiDevD2PadOrient       = OrientH;
  parameter pad_orient_e DioPadSpiDevD3PadOrient       = OrientH;
  parameter pad_orient_e DioPadSpiDevClkPadOrient      = OrientH;
  parameter pad_orient_e DioPadSpiDevCsLPadOrient      = OrientH;
  parameter pad_orient_e DioPadUsbPPadOrient           = OrientH;
  parameter pad_orient_e DioPadUsbNPadOrient           = OrientH;
  parameter pad_orient_e DioPadCc1PadOrient            = OrientH;
  parameter pad_orient_e DioPadCc2PadOrient            = OrientH;
  parameter pad_orient_e DioPadFlashTestVoltPadOrient  = OrientH;
  parameter pad_orient_e DioPadFlashTestMode0PadOrient = OrientH;
  parameter pad_orient_e DioPadFlashTestMode1PadOrient = OrientH;
  parameter pad_orient_e DioPadOtpExtVoltPadOrient     = OrientH;
  parameter pad_orient_e DioPadIor8PadOrient           = OrientV;
  parameter pad_orient_e DioPadIor9PadOrient           = OrientV;
  parameter pad_orient_e MioPadIoa0PadOrient           = OrientH;
  parameter pad_orient_e MioPadIoa1PadOrient           = OrientH;
  parameter pad_orient_e MioPadIoa2PadOrient           = OrientH;
  parameter pad_orient_e MioPadIoa3PadOrient           = OrientH;
  parameter pad_orient_e MioPadIoa4PadOrient           = OrientH;
  parameter pad_orient_e MioPadIoa5PadOrient           = OrientH;
  parameter pad_orient_e MioPadIoa6PadOrient           = OrientH;
  parameter pad_orient_e MioPadIoa7PadOrient           = OrientH;
  parameter pad_orient_e MioPadIoa8PadOrient           = OrientH;
  parameter pad_orient_e MioPadIob0PadOrient           = OrientH;
  parameter pad_orient_e MioPadIob1PadOrient           = OrientH;
  parameter pad_orient_e MioPadIob2PadOrient           = OrientH;
  parameter pad_orient_e MioPadIob3PadOrient           = OrientH;
  parameter pad_orient_e MioPadIob4PadOrient           = OrientH;
  parameter pad_orient_e MioPadIob5PadOrient           = OrientH;
  parameter pad_orient_e MioPadIob6PadOrient           = OrientH;
  parameter pad_orient_e MioPadIob7PadOrient           = OrientH;
  parameter pad_orient_e MioPadIob8PadOrient           = OrientH;
  parameter pad_orient_e MioPadIob9PadOrient           = OrientH;
  parameter pad_orient_e MioPadIob10PadOrient          = OrientH;
  parameter pad_orient_e MioPadIob11PadOrient          = OrientH;
  parameter pad_orient_e MioPadIob12PadOrient          = OrientH;
  parameter pad_orient_e MioPadIoc0PadOrient           = OrientH;
  parameter pad_orient_e MioPadIoc1PadOrient           = OrientH;
  parameter pad_orient_e MioPadIoc2PadOrient           = OrientH;
  parameter pad_orient_e MioPadIoc3PadOrient           = OrientH;
  parameter pad_orient_e MioPadIoc4PadOrient           = OrientH;
  parameter pad_orient_e MioPadIoc5PadOrient           = OrientH;
  parameter pad_orient_e MioPadIoc6PadOrient           = OrientH;
  parameter pad_orient_e MioPadIoc7PadOrient           = OrientH;
  parameter pad_orient_e MioPadIoc8PadOrient           = OrientH;
  parameter pad_orient_e MioPadIoc9PadOrient           = OrientH;
  parameter pad_orient_e MioPadIoc10PadOrient          = OrientH;
  parameter pad_orient_e MioPadIoc11PadOrient          = OrientH;
  parameter pad_orient_e MioPadIoc12PadOrient          = OrientH;
  parameter pad_orient_e MioPadIor0PadOrient           = OrientV;
  parameter pad_orient_e MioPadIor1PadOrient           = OrientV;
  parameter pad_orient_e MioPadIor2PadOrient           = OrientV;
  parameter pad_orient_e MioPadIor3PadOrient           = OrientV;
  parameter pad_orient_e MioPadIor4PadOrient           = OrientV;
  parameter pad_orient_e MioPadIor5PadOrient           = OrientV;
  parameter pad_orient_e MioPadIor6PadOrient           = OrientV;
  parameter pad_orient_e MioPadIor7PadOrient           = OrientV;
  parameter pad_orient_e MioPadIor10PadOrient          = OrientV;
  parameter pad_orient_e MioPadIor11PadOrient          = OrientV;
  parameter pad_orient_e MioPadIor12PadOrient          = OrientV;
  parameter pad_orient_e MioPadIor13PadOrient          = OrientV;

endpackage : pad_orient_pkg
