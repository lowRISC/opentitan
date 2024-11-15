// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Open-source scan role definitions for pads.
// This is only relevant for the ASIC target.

package scan_role_pkg;

  import prim_pad_wrapper_pkg::*;

  parameter scan_role_e DioPadPorNScanRole            = NoScan;
  parameter scan_role_e DioPadOtpExtVoltScanRole      = NoScan;
  parameter scan_role_e DioPadJtagTckScanRole         = NoScan;
  parameter scan_role_e DioPadJtagTmsScanRole         = NoScan;
  parameter scan_role_e DioPadJtagTdiScanRole         = NoScan;
  parameter scan_role_e DioPadJtagTdoScanRole         = NoScan;
  parameter scan_role_e DioPadJtagTrstNScanRole       = NoScan;
  parameter scan_role_e DioPadSpiHostD0ScanRole       = NoScan;
  parameter scan_role_e DioPadSpiHostD1ScanRole       = NoScan;
  parameter scan_role_e DioPadSpiHostD2ScanRole       = NoScan;
  parameter scan_role_e DioPadSpiHostD3ScanRole       = NoScan;
  parameter scan_role_e DioPadSpiHostClkScanRole      = NoScan;
  parameter scan_role_e DioPadSpiHostCsLScanRole      = NoScan;
  parameter scan_role_e DioPadSpiDevD0ScanRole        = NoScan;
  parameter scan_role_e DioPadSpiDevD1ScanRole        = NoScan;
  parameter scan_role_e DioPadSpiDevD2ScanRole        = NoScan;
  parameter scan_role_e DioPadSpiDevD3ScanRole        = NoScan;
  parameter scan_role_e DioPadSpiDevClkScanRole       = NoScan;
  parameter scan_role_e DioPadSpiDevCsLScanRole       = NoScan;
  parameter scan_role_e DioPadSpiDevTpmCsLScanRole    = NoScan;
  parameter scan_role_e DioPadUartRxScanRole          = NoScan;
  parameter scan_role_e DioPadUartTxScanRole          = NoScan;
  parameter scan_role_e DioPadI2cSclScanRole          = NoScan;
  parameter scan_role_e DioPadI2cSdaScanRole          = NoScan;
  parameter scan_role_e DioPadGpio0ScanRole           = NoScan;
  parameter scan_role_e DioPadGpio1ScanRole           = NoScan;
  parameter scan_role_e DioPadGpio2ScanRole           = NoScan;
  parameter scan_role_e DioPadGpio3ScanRole           = NoScan;
  parameter scan_role_e DioPadGpio4ScanRole           = NoScan;
  parameter scan_role_e DioPadGpio5ScanRole           = NoScan;
  parameter scan_role_e DioPadGpio6ScanRole           = NoScan;
  parameter scan_role_e DioPadGpio7ScanRole           = NoScan;
  parameter scan_role_e DioPadGpio8ScanRole           = NoScan;
  parameter scan_role_e DioPadGpio9ScanRole           = NoScan;
  parameter scan_role_e DioPadGpio10ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio11ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio12ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio13ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio14ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio15ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio16ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio17ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio18ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio19ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio20ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio21ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio22ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio23ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio24ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio25ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio26ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio27ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio28ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio29ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio30ScanRole          = NoScan;
  parameter scan_role_e DioPadGpio31ScanRole          = NoScan;
  parameter scan_role_e DioPadSocGpi0ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpi1ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpi2ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpi3ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpi4ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpi5ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpi6ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpi7ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpi8ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpi9ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpi10ScanRole        = NoScan;
  parameter scan_role_e DioPadSocGpi11ScanRole        = NoScan;
  parameter scan_role_e DioPadSocGpo0ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpo1ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpo2ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpo3ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpo4ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpo5ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpo6ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpo7ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpo8ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpo9ScanRole         = NoScan;
  parameter scan_role_e DioPadSocGpo10ScanRole        = NoScan;
  parameter scan_role_e DioPadSocGpo11ScanRole        = NoScan;
  parameter scan_role_e MioPadMio0ScanRole            = NoScan;
  parameter scan_role_e MioPadMio1ScanRole            = NoScan;
  parameter scan_role_e MioPadMio2ScanRole            = NoScan;
  parameter scan_role_e MioPadMio3ScanRole            = NoScan;
  parameter scan_role_e MioPadMio4ScanRole            = NoScan;
  parameter scan_role_e MioPadMio5ScanRole            = NoScan;
  parameter scan_role_e MioPadMio6ScanRole            = NoScan;
  parameter scan_role_e MioPadMio7ScanRole            = NoScan;
  parameter scan_role_e MioPadMio8ScanRole            = NoScan;
  parameter scan_role_e MioPadMio9ScanRole            = NoScan;
  parameter scan_role_e MioPadMio10ScanRole           = NoScan;
  parameter scan_role_e MioPadMio11ScanRole           = NoScan;

endpackage : scan_role_pkg
