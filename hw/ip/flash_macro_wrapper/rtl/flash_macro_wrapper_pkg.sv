// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Wrapper package.
//

package flash_macro_wrapper_pkg;

  typedef logic [7:0] fla_obs_t;

  // dft_en jtag selection
  typedef enum logic [2:0] {
    FlashLcTckSel,
    FlashLcTdiSel,
    FlashLcTmsSel,
    FlashLcTdoSel,
    FlashBistSel,
    FlashLcDftLast
  } flash_lc_jtag_e;

endpackage : flash_macro_wrapper_pkg
