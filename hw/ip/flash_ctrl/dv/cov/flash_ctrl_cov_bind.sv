// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds FLASH_CTRL functional coverage interface to the top level FLASH_CTRL module.
module flash_ctrl_cov_bind;
  bind flash_ctrl flash_ctrl_cov_if u_flash_ctrl_cov_if (.*);
endmodule
