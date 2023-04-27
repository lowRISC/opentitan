// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module usr_access_xil7series (
  output logic [31:0] info_o

);

  USR_ACCESSE2 u_fpga_info (
    .CFGCLK(),
    .DATA(info_o),
    .DATAVALID()
  );

endmodule // usr_access_xil7series
