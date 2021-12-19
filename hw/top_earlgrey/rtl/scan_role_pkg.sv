// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Open-source scan role definitions for pads.
// This is only relevant for the ASIC target.

package scan_role_pkg;

  import prim_pad_wrapper_pkg::*;

  parameter scan_role_e DioPadAstMiscScanRole         = NoScan;
  parameter scan_role_e DioPadPorNScanRole            = NoScan;
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
  parameter scan_role_e DioPadUsbPScanRole            = NoScan;
  parameter scan_role_e DioPadUsbNScanRole            = NoScan;
  parameter scan_role_e DioPadCc1ScanRole             = NoScan;
  parameter scan_role_e DioPadCc2ScanRole             = NoScan;
  parameter scan_role_e DioPadFlashTestVoltScanRole   = NoScan;
  parameter scan_role_e DioPadFlashTestMode0ScanRole  = NoScan;
  parameter scan_role_e DioPadFlashTestMode1ScanRole  = NoScan;
  parameter scan_role_e DioPadOtpExtVoltScanRole      = NoScan;
  parameter scan_role_e DioPadIor8ScanRole            = NoScan;
  parameter scan_role_e DioPadIor9ScanRole            = NoScan;
  parameter scan_role_e MioPadIoa0ScanRole            = NoScan;
  parameter scan_role_e MioPadIoa1ScanRole            = NoScan;
  parameter scan_role_e MioPadIoa2ScanRole            = NoScan;
  parameter scan_role_e MioPadIoa3ScanRole            = NoScan;
  parameter scan_role_e MioPadIoa4ScanRole            = NoScan;
  parameter scan_role_e MioPadIoa5ScanRole            = NoScan;
  parameter scan_role_e MioPadIoa6ScanRole            = NoScan;
  parameter scan_role_e MioPadIoa7ScanRole            = NoScan;
  parameter scan_role_e MioPadIoa8ScanRole            = NoScan;
  parameter scan_role_e MioPadIob0ScanRole            = NoScan;
  parameter scan_role_e MioPadIob1ScanRole            = NoScan;
  parameter scan_role_e MioPadIob2ScanRole            = NoScan;
  parameter scan_role_e MioPadIob3ScanRole            = NoScan;
  parameter scan_role_e MioPadIob4ScanRole            = NoScan;
  parameter scan_role_e MioPadIob5ScanRole            = NoScan;
  parameter scan_role_e MioPadIob6ScanRole            = NoScan;
  parameter scan_role_e MioPadIob7ScanRole            = NoScan;
  parameter scan_role_e MioPadIob8ScanRole            = NoScan;
  parameter scan_role_e MioPadIob9ScanRole            = NoScan;
  parameter scan_role_e MioPadIob10ScanRole           = NoScan;
  parameter scan_role_e MioPadIob11ScanRole           = NoScan;
  parameter scan_role_e MioPadIob12ScanRole           = NoScan;
  parameter scan_role_e MioPadIoc0ScanRole            = NoScan;
  parameter scan_role_e MioPadIoc1ScanRole            = NoScan;
  parameter scan_role_e MioPadIoc2ScanRole            = NoScan;
  parameter scan_role_e MioPadIoc3ScanRole            = NoScan;
  parameter scan_role_e MioPadIoc4ScanRole            = NoScan;
  parameter scan_role_e MioPadIoc5ScanRole            = NoScan;
  parameter scan_role_e MioPadIoc6ScanRole            = NoScan;
  parameter scan_role_e MioPadIoc7ScanRole            = NoScan;
  parameter scan_role_e MioPadIoc8ScanRole            = NoScan;
  parameter scan_role_e MioPadIoc9ScanRole            = NoScan;
  parameter scan_role_e MioPadIoc10ScanRole           = NoScan;
  parameter scan_role_e MioPadIoc11ScanRole           = NoScan;
  parameter scan_role_e MioPadIoc12ScanRole           = NoScan;
  parameter scan_role_e MioPadIor0ScanRole            = NoScan;
  parameter scan_role_e MioPadIor1ScanRole            = NoScan;
  parameter scan_role_e MioPadIor2ScanRole            = NoScan;
  parameter scan_role_e MioPadIor3ScanRole            = NoScan;
  parameter scan_role_e MioPadIor4ScanRole            = NoScan;
  parameter scan_role_e MioPadIor5ScanRole            = NoScan;
  parameter scan_role_e MioPadIor6ScanRole            = NoScan;
  parameter scan_role_e MioPadIor7ScanRole            = NoScan;
  parameter scan_role_e MioPadIor10ScanRole           = NoScan;
  parameter scan_role_e MioPadIor11ScanRole           = NoScan;
  parameter scan_role_e MioPadIor12ScanRole           = NoScan;
  parameter scan_role_e MioPadIor13ScanRole           = NoScan;

endpackage : scan_role_pkg
