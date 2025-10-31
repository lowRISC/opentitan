// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface to handle signal level code for the miscellaneous signals without an attached
// UVM agent
interface rram_ctrl_misc_io_if();
  // Dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import rram_ctrl_env_pkg::*;
  import rram_ctrl_test_pkg::*;

  // Macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Imports from packages
  // TODO

  // Variables corresponding to some of the DUT signals
  // TODO

  // Methods to manage rram_policy_bus
  // TODO: add handy functions

endinterface : rram_ctrl_misc_io_if
