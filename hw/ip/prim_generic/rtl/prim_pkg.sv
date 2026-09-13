// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package prim_pkg;
  // The name of the technology implementation.
  parameter PrimTechName = "Generic";

  // The minimum delay in cycles it can take a signal to propagate through a CDC prim_2sync flop.
  parameter int CdcMinDelayCycles = 1;

  function automatic int get_cdc_min_delay_cycles();
    return CdcMinDelayCycles;
  endfunction

endpackage // prim_pkg
