// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Abstract class meant to hold arbitrary virtual interface handles.
//
// Written primarily for an interface which implements functional coverage, this could be used
// for other purposes as well. This abstract class provides utilities & macros to retrieve
// virtual interface handles that are bound to a DUT's sub-modules. These sub-module interfaces must
// self-register using the `DV_VIF_WRAP_SET_VIF()` macro (see details below). The extended class
// then implements the `get_vifs()` method using the `DV_VIF_WRAP_GET_VIF*` macros below to retrieve
// the sub-module interface handles it maintains.
virtual class dv_vif_wrap;
  string hier;  // Represents the hierarchy of the parent module or interface.
  string name;  // Name of the class instance.

  function new(string hier, string name = "");
    this.hier = hier;
    this.name = name;
  endfunction

  // Abstract method implemented by the extended class. It is recommended to invoke the helper
  // macros below rather than manually define it.
  pure virtual task get_vifs();

endclass

// Helper macros.
//
// These are defined in the file itself since they are tightly coupled to the class definition
// above. These are scoped globally so that extended classes can invoke them.

// Enable an interface to register itself (set its handle into the config db).
//
// Meant to be invoked from an interface. The macros invocation causes the interface to register
// itself into the uvm_resource_db pool. The derived class of dv_vif_wrap retrieves the handle to
// that interface handle from the uvm_resource db pool.
//
// SV LRM does not yet allow referencing the instance of an interface within itself as one
// would in case of a class using the ~this~ keyword. However, most major simulators actually
// support this in their own custom way. On VCS, a reference to self within the interface can be set
// using `interface::self()` construct. On Xcelium, this is achieved by simply referencing the
// interface name.
//
// _IF:    The SV interface
// _VIF:   The corresponding virtual interface handle name
// _LEVEL: # of hierarchical levels the module to which the SV interface is bound, starting at the
//         top level DUT instance.
`define DV_VIF_WRAP_SET_VIF(_IF, _VIF, _LEVEL = 0) \
  import uvm_pkg::*; \
  function automatic void self_register(); \
    string path; \
    virtual _IF vif; \
    /* Initial block adds another level in the path hierarchy which needs to be split out. */ \
    /* Add one more to go one level up the interface instance. */ \
    /* Example: tb.dut.core.u_foo_if.self_register -> tb.dut.core. */ \
    path = dv_utils_pkg::get_parent_hier(.hier($sformatf("%m")), .n_levels_up(2 + _LEVEL)); \
`ifdef VCS \
  vif = interface::self(); \
`elsif XCELIUM \
  vif = _IF; \
`else \
  vif = _IF; \
`endif \
    uvm_pkg::uvm_resource_db#(virtual _IF)::set(path, `"_VIF`", vif); \
  endfunction \
  initial self_register();

// Enables the retrieval of individual vifs.
//
// The three macros below go together to define the _get_vifs() task in the extended class.
`define DV_VIF_WRAP_GET_VIFS_BEGIN \
  task get_vifs(); \
    fork \

// To avoid race condition between the instant when an interface handle is set into the config db
// and the instant when it is retrieved (in the same time step, at t = 0), the macro below invokes
// uvm_config_db#(..)::wait_modified() to ensure that the retrieval is done only after the set.
`define DV_VIF_WRAP_GET_VIF(_IF, _VIF) \
    begin \
      bit vif_found; \
      /* At most 2 retries. */ \
      repeat (2) begin \
        /* Force the evaluation at the end of the time step. */ \
        #0; \
        if (uvm_pkg::uvm_resource_db#(virtual _IF)::read_by_name(hier, `"_VIF`", _VIF)) begin \
          vif_found = 1'b1; \
          break; \
        end \
      end \
      `DV_CHECK_FATAL(vif_found, {`"_VIF`", " not found in the resource db"}, hier) \
    end

`define DV_VIF_WRAP_GET_VIFS_END \
    join \
  endtask
