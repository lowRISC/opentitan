// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// High-level goal
// ---------------
// - Exercises the *bypass* feature for AC_RANGE_CHECK.
// - Confirms that once RANGE_CHECK_OVERWRITE interface is set, The module is in bypass mode and the
//   design is transparent to all TLUL transactions on the TLUL unfiltered interface.
// - Runs live TLUL traffic to catch any functional issues.
//
// Key take-aways
// --------------
// - Verifies that AC_RANGE_CHECK has no implications on TLUL traffic
//------------------------------------------------------------------------------

class ${module_instance_name}_bypass_vseq extends ${module_instance_name}_smoke_vseq;
  `uvm_object_utils(${module_instance_name}_bypass_vseq)

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
endclass : ${module_instance_name}_bypass_vseq



function ${module_instance_name}_bypass_vseq::new(string name="");
  super.new(name);
endfunction : new

task ${module_instance_name}_bypass_vseq::body();

  // AC_RANGE_CHECK can only be set to bypass when 'range_check_overwrite' pins are set to 1
  // This interface is part of the misc intf in the TB and direct access is available via the cfg in
  // the TB.
  cfg.misc_vif.set_range_check_overwrite(1);

  super.body();
endtask : body
