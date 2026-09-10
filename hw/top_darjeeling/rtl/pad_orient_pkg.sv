// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Open-source pad orientation definitions.
// This is only relevant for the ASIC target.

package pad_orient_pkg;

  import prim_pad_wrapper_pkg::*;

  parameter pad_orient_e DioPadPorNPadOrient         = OrientH;
  parameter pad_orient_e DioPadOtpExtVoltPadOrient   = OrientH;
  parameter pad_orient_e DioPadJtagTckPadOrient      = OrientH;
  parameter pad_orient_e DioPadJtagTmsPadOrient      = OrientH;
  parameter pad_orient_e DioPadJtagTdiPadOrient      = OrientH;
  parameter pad_orient_e DioPadJtagTdoPadOrient      = OrientH;
  parameter pad_orient_e DioPadJtagTrstNPadOrient    = OrientH;
  parameter pad_orient_e DioPadSpiHostD0PadOrient    = OrientH;
  parameter pad_orient_e DioPadSpiHostD1PadOrient    = OrientH;
  parameter pad_orient_e DioPadSpiHostD2PadOrient    = OrientH;
  parameter pad_orient_e DioPadSpiHostD3PadOrient    = OrientH;
  parameter pad_orient_e DioPadSpiHostClkPadOrient   = OrientH;
  parameter pad_orient_e DioPadSpiHostCsLPadOrient   = OrientH;
  parameter pad_orient_e DioPadSpiDevD0PadOrient     = OrientH;
  parameter pad_orient_e DioPadSpiDevD1PadOrient     = OrientH;
  parameter pad_orient_e DioPadSpiDevD2PadOrient     = OrientH;
  parameter pad_orient_e DioPadSpiDevD3PadOrient     = OrientH;
  parameter pad_orient_e DioPadSpiDevClkPadOrient    = OrientH;
  parameter pad_orient_e DioPadSpiDevCsLPadOrient    = OrientH;
  parameter pad_orient_e DioPadSpiDevTpmCsLPadOrient = OrientH;
  parameter pad_orient_e DioPadUartRxPadOrient       = OrientH;
  parameter pad_orient_e DioPadUartTxPadOrient       = OrientH;
  parameter pad_orient_e DioPadI2cSclPadOrient       = OrientH;
  parameter pad_orient_e DioPadI2cSdaPadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio0PadOrient        = OrientH;
  parameter pad_orient_e DioPadGpio1PadOrient        = OrientH;
  parameter pad_orient_e DioPadGpio2PadOrient        = OrientH;
  parameter pad_orient_e DioPadGpio3PadOrient        = OrientH;
  parameter pad_orient_e DioPadGpio4PadOrient        = OrientH;
  parameter pad_orient_e DioPadGpio5PadOrient        = OrientH;
  parameter pad_orient_e DioPadGpio6PadOrient        = OrientH;
  parameter pad_orient_e DioPadGpio7PadOrient        = OrientH;
  parameter pad_orient_e DioPadGpio8PadOrient        = OrientH;
  parameter pad_orient_e DioPadGpio9PadOrient        = OrientH;
  parameter pad_orient_e DioPadGpio10PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio11PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio12PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio13PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio14PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio15PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio16PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio17PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio18PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio19PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio20PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio21PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio22PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio23PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio24PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio25PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio26PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio27PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio28PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio29PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio30PadOrient       = OrientH;
  parameter pad_orient_e DioPadGpio31PadOrient       = OrientH;
  parameter pad_orient_e DioPadSocGpi0PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpi1PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpi2PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpi3PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpi4PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpi5PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpi6PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpi7PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpi8PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpi9PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpi10PadOrient     = OrientH;
  parameter pad_orient_e DioPadSocGpi11PadOrient     = OrientH;
  parameter pad_orient_e DioPadSocGpo0PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpo1PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpo2PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpo3PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpo4PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpo5PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpo6PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpo7PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpo8PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpo9PadOrient      = OrientH;
  parameter pad_orient_e DioPadSocGpo10PadOrient     = OrientH;
  parameter pad_orient_e DioPadSocGpo11PadOrient     = OrientH;
  parameter pad_orient_e MioPadMio0PadOrient         = OrientH;
  parameter pad_orient_e MioPadMio1PadOrient         = OrientH;
  parameter pad_orient_e MioPadMio2PadOrient         = OrientH;
  parameter pad_orient_e MioPadMio3PadOrient         = OrientH;
  parameter pad_orient_e MioPadMio4PadOrient         = OrientH;
  parameter pad_orient_e MioPadMio5PadOrient         = OrientH;
  parameter pad_orient_e MioPadMio6PadOrient         = OrientH;
  parameter pad_orient_e MioPadMio7PadOrient         = OrientH;
  parameter pad_orient_e MioPadMio8PadOrient         = OrientH;
  parameter pad_orient_e MioPadMio9PadOrient         = OrientH;
  parameter pad_orient_e MioPadMio10PadOrient        = OrientH;
  parameter pad_orient_e MioPadMio11PadOrient        = OrientH;

endpackage : pad_orient_pkg
