// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module kmac_cov_bind;
  bind kmac cip_mubi_cov_if #(.Width(4)) kmac_sha3_done_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (sha3_done)
  );

    bind kmac cip_mubi_cov_if #(.Width(4)) kmac_sha3_absorb_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (sha3_absorbed)
  );

endmodule
