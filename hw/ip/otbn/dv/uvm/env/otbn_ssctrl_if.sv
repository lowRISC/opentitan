// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Bound into dut and used to help control assertions

// This interface uses hierarchical references to control some assertions inside the design.
// This can then be used by virtual sequences (which can't use hierarchical references directly)

`define SSCTRL_HPATH tb.dut.u_otbn_core.u_otbn_start_stop_control
`define SSCTRL_PATH  `"`SSCTRL_HPATH`"

interface otbn_ssctrl_if;

  function automatic string resolve_path(string signal);
    return {`SSCTRL_PATH, ".", signal};
  endfunction

  function automatic void control_secwipe_running_assertion(bit enable);
    if (enable) $asserton(0, `SSCTRL_HPATH.StartSecureWipeImpliesRunning_A);
    else $assertoff(0, `SSCTRL_HPATH.StartSecureWipeImpliesRunning_A);
  endfunction

endinterface

`undef SSCTRL_HPATH
`undef SSCTRL_PATH
