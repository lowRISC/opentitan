// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package env_dpi;

  import "DPI-C"
  function void env_initial(input bit [31:0] seed,
                            input bit        PMPEnable,
                            input bit [31:0] PMPGranularity,
                            input bit [31:0] PMPNumRegions);

  import "DPI-C"
  function void env_final();

  import "DPI-C"
  function void env_tick(
    output bit stop_req);

endpackage


