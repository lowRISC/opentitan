// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef UVM
  `include "uvm_macros.svh"
`endif

// UVM speficic macros
`ifndef gfn
`ifdef UVM
  // verilog_lint: waive macro-name-style
  `define gfn get_full_name()
`else
  // verilog_lint: waive macro-name-style
  `define gfn $sformatf("%m")
`endif
`endif

`ifndef gtn
  // verilog_lint: waive macro-name-style
  `define gtn get_type_name()
`endif

`ifndef gn
  // verilog_lint: waive macro-name-style
  `define gn get_name()
`endif

`ifndef gmv
  // verilog_lint: waive macro-name-style
  `define gmv(csr) csr.get_mirrored_value()
`endif

// cast base class obj holding extended class handle to extended class handle;
// throw error if cast fails
`ifndef downcast
  // verilog_lint: waive macro-name-style
  `define downcast(EXT_, BASE_, MSG_="", SEV_=fatal, ID_=`gfn) \
    begin \
      if (!$cast(EXT_, BASE_)) begin \
        `dv_``SEV_($sformatf({"Cast failed: base class variable %0s ", \
                              "does not hold extended class %0s handle %s"}, \
                              `"BASE_`", `"EXT_`", MSG_), ID_) \
      end \
    end
`endif

// Note, UVM provides a macro `uvm_new_func -- which only applies to uvm_components
`ifndef uvm_object_new
  `define uvm_object_new \
    function new (string name=""); \
      super.new(name); \
    endfunction : new
`endif

`ifndef uvm_create_obj
  `define uvm_create_obj(_type_name_, _inst_name_) \
    _inst_name_ = _type_name_::type_id::create(`"_inst_name_`");
`endif

`ifndef uvm_component_new
  `define uvm_component_new \
    function new (string name="", uvm_component parent=null); \
      super.new(name, parent); \
    endfunction : new
`endif

`ifndef uvm_create_comp
  `define uvm_create_comp(_type_name_, _inst_name_) \
    _inst_name_ = _type_name_::type_id::create(`"_inst_name_`", this);
`endif

// Convert arbitrary text / expression to string.
`ifndef DV_STRINGIFY
  `define DV_STRINGIFY(I_) `"I_`"
`endif

// Common check macros used by DV_CHECK error and fatal macros.
// Note: Should not be called by user code
`ifndef DV_CHECK
  `define DV_CHECK(T_, MSG_="", SEV_=error, ID_=`gfn) \
    begin \
      if (!(T_)) begin \
        `dv_``SEV_($sformatf("Check failed (%s) %s ", `"T_`", MSG_), ID_) \
      end \
    end
`endif

`ifndef DV_CHECK_EQ
  `define DV_CHECK_EQ(ACT_, EXP_, MSG_="", SEV_=error, ID_=`gfn) \
    begin \
      if (!((ACT_) == (EXP_))) begin \
        `dv_``SEV_($sformatf("Check failed %s == %s (%0d [0x%0h] vs %0d [0x%0h]) %s", \
                             `"ACT_`", `"EXP_`", ACT_, ACT_, EXP_, EXP_, MSG_), ID_) \
      end \
    end
`endif

`ifndef DV_CHECK_NE
  `define DV_CHECK_NE(ACT_, EXP_, MSG_="", SEV_=error, ID_=`gfn) \
    begin \
      if (!((ACT_) != (EXP_))) begin \
        `dv_``SEV_($sformatf("Check failed %s != %s (%0d [0x%0h] vs %0d [0x%0h]) %s", \
                             `"ACT_`", `"EXP_`", ACT_, ACT_, EXP_, EXP_, MSG_), ID_) \
      end \
    end
`endif

`ifndef DV_CHECK_CASE_EQ
  `define DV_CHECK_CASE_EQ(ACT_, EXP_, MSG_="", SEV_=error, ID_=`gfn) \
    begin \
      if (!((ACT_) === (EXP_))) begin \
        `dv_``SEV_($sformatf("Check failed %s === %s (0x%0h [%0b] vs 0x%0h [%0b]) %s", \
                             `"ACT_`", `"EXP_`", ACT_, ACT_, EXP_, EXP_, MSG_), ID_) \
      end \
    end
`endif

`ifndef DV_CHECK_CASE_NE
  `define DV_CHECK_CASE_NE(ACT_, EXP_, MSG_="", SEV_=error, ID_=`gfn) \
    begin \
      if (!((ACT_) !== (EXP_))) begin \
        `dv_``SEV_($sformatf("Check failed %s !== %s (%0d [0x%0h] vs %0d [0x%0h]) %s", \
                             `"ACT_`", `"EXP_`", ACT_, ACT_, EXP_, EXP_, MSG_), ID_) \
      end \
    end
`endif

`ifndef DV_CHECK_LT
  `define DV_CHECK_LT(ACT_, EXP_, MSG_="", SEV_=error, ID_=`gfn) \
    begin \
      if (!((ACT_) < (EXP_))) begin \
        `dv_``SEV_($sformatf("Check failed %s < %s (%0d [0x%0h] vs %0d [0x%0h]) %s", \
                             `"ACT_`", `"EXP_`", ACT_, ACT_, EXP_, EXP_, MSG_), ID_) \
      end \
    end
`endif

`ifndef DV_CHECK_GT
  `define DV_CHECK_GT(ACT_, EXP_, MSG_="", SEV_=error, ID_=`gfn) \
    begin \
      if (!((ACT_) > (EXP_))) begin \
        `dv_``SEV_($sformatf("Check failed %s > %s (%0d [0x%0h] vs %0d [0x%0h]) %s", \
                             `"ACT_`", `"EXP_`", ACT_, ACT_, EXP_, EXP_, MSG_), ID_) \
      end \
    end
`endif

`ifndef DV_CHECK_LE
  `define DV_CHECK_LE(ACT_, EXP_, MSG_="", SEV_=error, ID_=`gfn) \
    begin \
      if (!((ACT_) <= (EXP_))) begin \
        `dv_``SEV_($sformatf("Check failed %s <= %s (%0d [0x%0h] vs %0d [0x%0h]) %s", \
                             `"ACT_`", `"EXP_`", ACT_, ACT_, EXP_, EXP_, MSG_), ID_) \
      end \
    end
`endif

`ifndef DV_CHECK_GE
  `define DV_CHECK_GE(ACT_, EXP_, MSG_="", SEV_=error, ID_=`gfn) \
    begin \
      if (!((ACT_) >= (EXP_))) begin \
        `dv_``SEV_($sformatf("Check failed %s >= %s (%0d [0x%0h] vs %0d [0x%0h]) %s", \
                             `"ACT_`", `"EXP_`", ACT_, ACT_, EXP_, EXP_, MSG_), ID_) \
      end \
    end
`endif

`ifndef DV_CHECK_STREQ
  `define DV_CHECK_STREQ(ACT_, EXP_, MSG_="", SEV_=error, ID_=`gfn) \
    if (!((ACT_) == (EXP_))) begin \
      `dv_``SEV_($sformatf("Check failed \"%s\" == \"%s\" %s", ACT_, EXP_, MSG_), ID_) \
    end
`endif

`ifndef DV_CHECK_STRNE
  `define DV_CHECK_STRNE(ACT_, EXP_, MSG_="", SEV_=error, ID_=`gfn) \
    if (!((ACT_) != (EXP_))) begin \
      `dv_``SEV_($sformatf("Check failed \"%s\" != \"%s\" %s", ACT_, EXP_, MSG_), ID_) \
    end
`endif

// Fatal version of the checks
`ifndef DV_CHECK_FATAL
  `define DV_CHECK_FATAL(T_, MSG_="", ID_=`gfn) \
    `DV_CHECK(T_, MSG_, fatal, ID_)
`endif

`ifndef DV_CHECK_EQ_FATAL
  `define DV_CHECK_EQ_FATAL(ACT_, EXP_, MSG_="", ID_=`gfn) \
    `DV_CHECK_EQ(ACT_, EXP_, MSG_, fatal, ID_)
`endif

`ifndef DV_CHECK_NE_FATAL
  `define DV_CHECK_NE_FATAL(ACT_, EXP_, MSG_="", ID_=`gfn) \
    `DV_CHECK_NE(ACT_, EXP_, MSG_, fatal, ID_)
`endif

`ifndef DV_CHECK_LT_FATAL
  `define DV_CHECK_LT_FATAL(ACT_, EXP_, MSG_="", ID_=`gfn) \
    `DV_CHECK_LT(ACT_, EXP_, MSG_, fatal, ID_)
`endif

`ifndef DV_CHECK_GT_FATAL
  `define DV_CHECK_GT_FATAL(ACT_, EXP_, MSG_="", ID_=`gfn) \
    `DV_CHECK_GT(ACT_, EXP_, MSG_, fatal, ID_)
`endif

`ifndef DV_CHECK_LE_FATAL
  `define DV_CHECK_LE_FATAL(ACT_, EXP_, MSG_="", ID_=`gfn) \
    `DV_CHECK_LE(ACT_, EXP_, MSG_, fatal, ID_)
`endif

`ifndef DV_CHECK_GE_FATAL
  `define DV_CHECK_GE_FATAL(ACT_, EXP_, MSG_="", ID_=`gfn) \
    `DV_CHECK_GE(ACT_, EXP_, MSG_, fatal, ID_)
`endif

`ifndef DV_CHECK_STREQ_FATAL
  `define DV_CHECK_STREQ_FATAL(ACT_, EXP_, MSG_="", ID_=`gfn) \
    `DV_CHECK_STREQ(ACT_, EXP_, MSG_, fatal, ID_)
`endif

`ifndef DV_CHECK_STRNE_FATAL
  `define DV_CHECK_STRNE_FATAL(ACT_, EXP_, MSG_="", ID_=`gfn) \
    `DV_CHECK_STRNE(ACT_, EXP_, MSG_, fatal, ID_)
`endif

// Shorthand for common foo.randomize() + fatal check
`ifndef DV_CHECK_RANDOMIZE_FATAL
  `define DV_CHECK_RANDOMIZE_FATAL(VAR_, MSG_="Randomization failed!", ID_=`gfn) \
    `DV_CHECK_FATAL(VAR_.randomize(), MSG_, ID_)
`endif

// Shorthand for common foo.randomize() with { } + fatal check
`ifndef DV_CHECK_RANDOMIZE_WITH_FATAL
  `define DV_CHECK_RANDOMIZE_WITH_FATAL(VAR_, WITH_C_, MSG_="Randomization failed!", ID_=`gfn) \
    `DV_CHECK_FATAL(VAR_.randomize() with {WITH_C_}, MSG_, ID_)
`endif

// Shorthand for common std::randomize(foo) + fatal check
`ifndef DV_CHECK_STD_RANDOMIZE_FATAL
  `define DV_CHECK_STD_RANDOMIZE_FATAL(VAR_, MSG_="Randomization failed!", ID_=`gfn) \
    `DV_CHECK_FATAL(std::randomize(VAR_), MSG_, ID_)
`endif

// Shorthand for common std::randomize(foo) with { } + fatal check
`ifndef DV_CHECK_STD_RANDOMIZE_WITH_FATAL
  `define DV_CHECK_STD_RANDOMIZE_WITH_FATAL(VAR_, WITH_C_, MSG_="Randomization failed!",ID_=`gfn) \
    `DV_CHECK_FATAL(std::randomize(VAR_) with {WITH_C_}, MSG_, ID_)
`endif

// Shorthand for common cls_inst.randomize(member) + fatal check
// Randomizes a specific member of a class instance.
`ifndef DV_CHECK_MEMBER_RANDOMIZE_FATAL
  `define DV_CHECK_MEMBER_RANDOMIZE_FATAL(VAR_, CLS_INST_=this, MSG_="Randomization failed!", ID_=`gfn) \
    `DV_CHECK_FATAL(CLS_INST_.randomize(VAR_), MSG_, ID_)
`endif

// Shorthand for common cls_inst.randomize(member) with { } + fatal check
// Randomizes a specific member of a class instance with inline constraints.
`ifndef DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL
  `define DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(VAR_, C_, CLS_INST_=this, MSG_="Randomization failed!", ID_=`gfn) \
    `DV_CHECK_FATAL(CLS_INST_.randomize(VAR_) with {C_}, MSG_, ID_)
`endif

// print static/dynamic 1d array or queue
`ifndef DV_PRINT_ARR_CONTENTS
`define DV_PRINT_ARR_CONTENTS(ARR_, V_=uvm_pkg::UVM_MEDIUM, ID_=`gfn) \
  begin \
    foreach (ARR_[i]) begin \
      `dv_info($sformatf("%s[%0d] = %0d (0x%0h)", `"ARR_`", i, ARR_[i], ARR_[i]), V_, ID_) \
    end \
  end
`endif

// print non-empty tlm fifos that were uncompared at end of test
`ifndef DV_EOT_PRINT_TLM_FIFO_CONTENTS
`define DV_EOT_PRINT_TLM_FIFO_CONTENTS(TYP_, FIFO_, SEV_=error, ID_=`gfn) \
  begin \
    while (!FIFO_.is_empty()) begin \
      TYP_ item; \
      void'(FIFO_.try_get(item)); \
      `dv_``SEV_($sformatf("%s item uncompared:\n%s", `"FIFO_`", item.sprint()), ID_) \
    end \
  end
`endif

// print non-empty tlm fifos that were uncompared at end of test
`ifndef DV_EOT_PRINT_TLM_FIFO_ARR_CONTENTS
`define DV_EOT_PRINT_TLM_FIFO_ARR_CONTENTS(TYP_, FIFO_, SEV_=error, ID_=`gfn) \
  begin \
    foreach (FIFO_[i]) begin \
      while (!FIFO_[i].is_empty()) begin \
        TYP_ item; \
        void'(FIFO_[i].try_get(item)); \
        `dv_``SEV_($sformatf("%s[%0d] item uncompared:\n%s", `"FIFO_`", i, item.sprint()), ID_) \
      end \
    end \
  end
`endif

// print non-empty tlm fifos that were uncompared at end of test
`ifndef DV_EOT_PRINT_Q_CONTENTS
`define DV_EOT_PRINT_Q_CONTENTS(TYP_, Q_, SEV_=error, ID_=`gfn) \
  begin \
    while (Q_.size() != 0) begin \
      TYP_ item = Q_.pop_front(); \
      `dv_``SEV_($sformatf("%s item uncompared:\n%s", `"Q_`", item.sprint()), ID_) \
    end \
  end
`endif

// print non-empty tlm fifos that were uncompared at end of test
`ifndef DV_EOT_PRINT_Q_ARR_CONTENTS
`define DV_EOT_PRINT_Q_ARR_CONTENTS(TYP_, Q_, SEV_=error, ID_=`gfn) \
  begin \
    foreach (Q_[i]) begin \
      while (Q_[i].size() != 0) begin \
        TYP_ item = Q_[i].pop_front(); \
        `dv_``SEV_($sformatf("%s[%0d] item uncompared:\n%s", `"Q_`", i, item.sprint()), ID_) \
      end \
    end \
  end
`endif

// check for non-empty mailbox and print items that were uncompared at end of test
`ifndef DV_EOT_PRINT_MAILBOX_CONTENTS
`define DV_EOT_PRINT_MAILBOX_CONTENTS(TYP_, MAILBOX_, SEV_=error, ID_=`gfn) \
  begin \
    while (MAILBOX_.num() != 0) begin \
      TYP_ item; \
      void'(MAILBOX_.try_get(item)); \
      `dv_``SEV_($sformatf("%s item uncompared:\n%s", `"MAILBOX_`", item.sprint()), ID_) \
    end \
  end
`endif

// get parity - implemented as a macro so that it can be invoked in constraints as well
`ifndef GET_PARITY
  `define GET_PARITY(val, odd=0) (^val ^ odd)
`endif

// Wait a task or statement with exit condition
// Kill the thread when either the wait statement is completed or exit condition occurs
// input WAIT_ need to be a statement. Here are some examples
// `DV_SPINWAIT(wait(...);, "Wait for ...")
// `DV_SPINWAIT(
//              while (1) begin
//                ...
//              end)
`ifndef DV_SPINWAIT_EXIT
`define DV_SPINWAIT_EXIT(WAIT_, EXIT_, MSG_ = "exit condition occurred!", ID_ =`gfn) \
  begin \
    fork begin \
      fork \
        begin \
          WAIT_ \
        end \
        begin \
          EXIT_ \
          if (MSG_ != "") begin \
            `dv_info(MSG_, uvm_pkg::UVM_HIGH, ID_) \
          end \
        end \
      join_any \
      disable fork; \
    end join \
  end
`endif

// wait a task or statement with timer watchdog
`ifndef DV_SPINWAIT
`define DV_SPINWAIT(WAIT_, MSG_ = "timeout occurred!", TIMEOUT_NS_ = default_spinwait_timeout_ns, ID_ =`gfn) \
  `DV_SPINWAIT_EXIT(WAIT_, wait_timeout(TIMEOUT_NS_, ID_, MSG_);, "", ID_)
`endif

// Control assertions in the DUT.
//
// This macro is invoked in top level testbench that instantiates the DUT. It spawns off an initial
// block that forever waits for a resource of type bit named by the string arg ~LABEL_~ that
// can be set by any entity in the testbench. Based on the value set, it enables or disables the
// assertions at the hierarchy of the provided path. The entity setting the resource value invokes
// uvm_config_db#(bit)::set(...) and this macro calls the corresponding get.
//
// LABEL_ : Name of the assertion control resource bit (string).
// HIER_  : Path to the module within which the assertion is controlled.
// LEVELS_: Number of levels within the module to control the assertions.
// SCOPE_ : Hierarchical string path to the testbench where this macro is invoked, example: %m.
// ID_    : Identifier string used for UVM logs.
`ifndef DV_ASSERT_CTRL
`define DV_ASSERT_CTRL(LABEL_, HIER_, LEVELS_ = 0, SCOPE_ = "", ID_ = "%m") \
  initial begin \
    bit assert_en; \
    forever begin \
      uvm_config_db#(bit)::wait_modified(null, SCOPE_, LABEL_); \
      if (!uvm_config_db#(bit)::get(null, SCOPE_, LABEL_, assert_en)) begin \
        `uvm_fatal(ID_, $sformatf("Failed to get \"%0s\" from uvm_config_db", LABEL_)) \
      end \
      if (assert_en) begin \
        `uvm_info(ID_, $sformatf("Enabling assertions: %0s", `DV_STRINGIFY(HIER_)), UVM_LOW) \
        $asserton(LEVELS_, HIER_); \
      end else begin \
        `uvm_info(ID_, $sformatf("Disabling assertions: %0s", `DV_STRINGIFY(HIER_)), UVM_LOW) \
        $assertoff(LEVELS_, HIER_); \
      end \
    end \
  end
`endif

// Enable / disable assertions at a module hierarchy identified by LABEL_.
//
// This goes in conjunction with `DV_ASSERT_CTRL() macro above, but is invoked in the entity that is
// sending the req to turn on / off the assertions. Note that that piece of code invoking this macro
// does not have the information on the actual hierarchical path to the module or the levels - this
// is 'wrapped' into the LABEL_ instead. DV user needs to uniquify the label sufficienly enough to
// reflect it.
//
// LABEL_ : Name of the assertion control resource bit (string).
// VALUE_ : Value of the control bit - 1 - enable assertions, 0 - disable assertions.
// SCOPE_ : Hierarchical string path to the testbench where this macro is invoked, example: %m.
`ifndef DV_ASSERT_CTRL_REQ
`define DV_ASSERT_CTRL_REQ(LABEL_, VALUE_, SCOPE_="") \
  begin \
    uvm_config_db#(bit)::set(null, SCOPE_, LABEL_, VALUE_); \
  end
`endif

// Macros for logging (info, warning, error and fatal severities).
//
// These are meant to be invoked in modules and interfaces that are shared between DV and Verilator
// testbenches. We waive the lint requirement for these to be in uppercase, since they are
// UVM-adjacent.
`ifdef UVM
`ifndef dv_info
  // verilog_lint: waive macro-name-style
  `define dv_info(MSG_,  VERBOSITY_ = uvm_pkg::UVM_LOW, ID_ = $sformatf("%m")) \
    if (uvm_pkg::uvm_report_enabled(VERBOSITY_, uvm_pkg::UVM_INFO, ID_)) begin \
        uvm_pkg::uvm_report_info(ID_, MSG_, VERBOSITY_, `uvm_file, `uvm_line, "", 1); \
    end
`endif

`ifndef dv_warning
  // verilog_lint: waive macro-name-style
  `define dv_warning(MSG_, ID_ = $sformatf("%m")) \
    if (uvm_pkg::uvm_report_enabled(uvm_pkg::UVM_NONE, uvm_pkg::UVM_WARNING, ID_)) begin \
        uvm_pkg::uvm_report_warning(ID_, MSG_, uvm_pkg::UVM_NONE, `uvm_file, `uvm_line, "", 1); \
    end
`endif

`ifndef dv_error
  // verilog_lint: waive macro-name-style
  `define dv_error(MSG_, ID_ = $sformatf("%m")) \
    if (uvm_pkg::uvm_report_enabled(uvm_pkg::UVM_NONE, uvm_pkg::UVM_ERROR, ID_)) begin \
        uvm_pkg::uvm_report_error(ID_, MSG_, uvm_pkg::UVM_NONE, `uvm_file, `uvm_line, "", 1); \
    end
`endif

`ifndef dv_fatal
  // verilog_lint: waive macro-name-style
  `define dv_fatal(MSG_, ID_ = $sformatf("%m")) \
    if (uvm_pkg::uvm_report_enabled(uvm_pkg::UVM_NONE, uvm_pkg::UVM_FATAL, ID_)) begin \
        uvm_pkg::uvm_report_fatal(ID_, MSG_, uvm_pkg::UVM_NONE, `uvm_file, `uvm_line, "", 1); \
    end
`endif

`else // UVM

`ifndef dv_info
  // verilog_lint: waive macro-name-style
  `define dv_info(MSG_, VERBOSITY = DUMMY_, ID_ = $sformatf("%m")) \
    $display("%0t: (%0s:%0d) [%0s] %0s", $time, `__FILE__, `__LINE__, ID_, MSG_);
`endif

`ifndef dv_warning
  // verilog_lint: waive macro-name-style
  `define dv_warning(MSG_, ID_ = $sformatf("%m")) \
    $warning("%0t: (%0s:%0d) [%0s] %0s", $time, `__FILE__, `__LINE__, ID_, MSG_);
`endif

`ifndef dv_error
  // verilog_lint: waive macro-name-style
  `define dv_error(MSG_, ID_ = $sformatf("%m")) \
    $error("%0t: (%0s:%0d) [%0s] %0s", $time, `__FILE__, `__LINE__, ID_, MSG_);
`endif

`ifndef dv_fatal
  // verilog_lint: waive macro-name-style
  `define dv_fatal(MSG_, ID_ = $sformatf("%m")) \
    $fatal("%0t: (%0s:%0d) [%0s] %0s", $time, `__FILE__, `__LINE__, ID_, MSG_);
`endif

`endif // UVM
