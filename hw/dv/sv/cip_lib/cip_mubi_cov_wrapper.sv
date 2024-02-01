// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This is a wrapper module for IPs to bind an array of mubi types port.
module cip_mubi_cov_wrapper
#(
  parameter int NumMubis = 1,
  parameter int Width    = 4  // parameter for cip_mubi_cov_if module
) (
  input [NumMubis-1:0][Width-1:0] mubis,
  input rst_ni
);

  for (genvar k = 0; k < NumMubis; k++) begin : gen_mubi_cov_if
    cip_mubi_cov_if#(Width) mubi_cov_if(.mubi(mubis[k]), .rst_ni(rst_ni));
  end
endmodule
