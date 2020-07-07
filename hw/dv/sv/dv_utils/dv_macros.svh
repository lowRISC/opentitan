// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// UVM speficic macros
`ifndef gfn
  `define gfn get_full_name()
`endif

`ifndef gtn
  `define gtn get_type_name()
`endif

`ifndef gn
  `define gn get_name()
`endif

`ifndef gmv
  `define gmv(csr) csr.get_mirrored_value()
`endif

// cast base class obj holding extended class handle to extended class handle;
// throw error if cast fails
`ifndef downcast
  `define downcast(EXT_, BASE_, MSG_="", SEV_=fatal, ID_=`gfn) \
    begin \
      if (!$cast(EXT_, BASE_)) begin \
        `uvm_``SEV_(ID_, $sformatf({"Cast failed: base class variable %0s ", \
                                    "does not hold extended class %0s handle %s"}, \
                                    `"BASE_`", `"EXT_`", MSG_)) \
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

// Common check macros used by DV_CHECK error and fatal macros.
// Note: Should not be called by user code
`ifndef DV_CHECK
  `define DV_CHECK(T_, MSG_="", SEV_=error, ID_=`gfn) \
    begin \
      if (!(T_)) begin \
        `uvm_``SEV_(ID_, $sformatf("Check failed (%s) %s ", `"T_`", MSG_)) \
      end \
    end
`endif

`ifndef DV_CHECK_EQ
  `define DV_CHECK_EQ(ACT_, EXP_, MSG_="", SEV_=error, ID_=`gfn) \
    begin \
      if (!(ACT_ == EXP_)) begin \
        `uvm_``SEV_(ID_, $sformatf("Check failed %s == %s (%0d [0x%0h] vs %0d [0x%0h]) %s", \
                                    `"ACT_`", `"EXP_`", ACT_, ACT_, EXP_, EXP_, MSG_)) \
      end \
    end
`endif

`ifndef DV_CHECK_NE
  `define DV_CHECK_NE(ACT_, EXP_, MSG_="", SEV_=error, ID_=`gfn) \
    begin \
      if (!(ACT_ != EXP_)) begin \
        `uvm_``SEV_(ID_, $sformatf("Check failed %s != %s (%0d [0x%0h] vs %0d [0x%0h]) %s", \
                                    `"ACT_`", `"EXP_`", ACT_, ACT_, EXP_, EXP_, MSG_)) \
      end \
    end
`endif

`ifndef DV_CHECK_CASE_EQ
  `define DV_CHECK_CASE_EQ(ACT_, EXP_, MSG_="", SEV_=error, ID_=`gfn) \
    begin \
      if (!(ACT_ === EXP_)) begin \
        `uvm_``SEV_(ID_, $sformatf("Check failed %s === %s (0x%0h [%0b] vs 0x%0h [%0b]) %s", \
                                    `"ACT_`", `"EXP_`", ACT_, ACT_, EXP_, EXP_, MSG_)) \
      end \
    end
`endif

`ifndef DV_CHECK_CASE_NE
  `define DV_CHECK_CASE_NE(ACT_, EXP_, MSG_="", SEV_=error, ID_=`gfn) \
    begin \
      if (!(ACT_ !== EXP_)) begin \
        `uvm_``SEV_(ID_, $sformatf("Check failed %s !== %s (%0d [0x%0h] vs %0d [0x%0h]) %s", \
                                    `"ACT_`", `"EXP_`", ACT_, ACT_, EXP_, EXP_, MSG_)) \
      end \
    end
`endif

`ifndef DV_CHECK_LT
  `define DV_CHECK_LT(ACT_, EXP_, MSG_="", SEV_=error, ID_=`gfn) \
    begin \
      if (!(ACT_ < EXP_)) begin \
        `uvm_``SEV_(ID_, $sformatf("Check failed %s < %s (%0d [0x%0h] vs %0d [0x%0h]) %s", \
                                    `"ACT_`", `"EXP_`", ACT_, ACT_, EXP_, EXP_, MSG_)) \
      end \
    end
`endif

`ifndef DV_CHECK_GT
  `define DV_CHECK_GT(ACT_, EXP_, MSG_="", SEV_=error, ID_=`gfn) \
    begin \
      if (!(ACT_ > EXP_)) begin \
        `uvm_``SEV_(ID_, $sformatf("Check failed %s > %s (%0d [0x%0h] vs %0d [0x%0h]) %s", \
                                    `"ACT_`", `"EXP_`", ACT_, ACT_, EXP_, EXP_, MSG_)) \
      end \
    end
`endif

`ifndef DV_CHECK_LE
  `define DV_CHECK_LE(ACT_, EXP_, MSG_="", SEV_=error, ID_=`gfn) \
    begin \
      if (!(ACT_ <= EXP_)) begin \
        `uvm_``SEV_(ID_, $sformatf("Check failed %s <= %s (%0d [0x%0h] vs %0d [0x%0h]) %s", \
                                    `"ACT_`", `"EXP_`", ACT_, ACT_, EXP_, EXP_, MSG_)) \
      end \
    end
`endif

`ifndef DV_CHECK_GE
  `define DV_CHECK_GE(ACT_, EXP_, MSG_="", SEV_=error, ID_=`gfn) \
    begin \
      if (!(ACT_ >= EXP_)) begin \
        `uvm_``SEV_(ID_, $sformatf("Check failed %s >= %s (%0d [0x%0h] vs %0d [0x%0h]) %s", \
                                    `"ACT_`", `"EXP_`", ACT_, ACT_, EXP_, EXP_, MSG_)) \
      end \
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

// Shorthand for common this.randomize(foo) + fatal check
`ifndef DV_CHECK_MEMBER_RANDOMIZE_FATAL
  `define DV_CHECK_MEMBER_RANDOMIZE_FATAL(VAR_, MSG_="Randomization failed!", ID_=`gfn) \
    `DV_CHECK_FATAL(this.randomize(VAR_), MSG_, ID_)
`endif

// Shorthand for common this.randomize(foo) with { } + fatal check
`ifndef DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL
  `define DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(VAR_, C_, MSG_="Randomization failed!", ID_=`gfn) \
    `DV_CHECK_FATAL(this.randomize(VAR_) with {C_}, MSG_, ID_)
`endif

// print static/dynamic 1d array or queue
`ifndef DV_PRINT_ARR_CONTENTS
`define DV_PRINT_ARR_CONTENTS(ARR_, V_=UVM_MEDIUM, ID_=`gfn) \
  begin \
    foreach (ARR_[i]) begin \
      `uvm_info(ID_, $sformatf("%s[%0d] = 0x%0d[0x%0h]", `"ARR_`", i, ARR_[i], ARR_[i]), V_) \
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
      `uvm_``SEV_(ID_, $sformatf("%s item uncompared:\n%s", `"FIFO_`", item.sprint())) \
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
        `uvm_``SEV_(ID_, $sformatf("%s[%0d] item uncompared:\n%s", `"FIFO_`", i, item.sprint())) \
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
      `uvm_``SEV_(ID_, $sformatf("%s item uncompared:\n%s", `"Q_`", item.sprint())) \
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
        `uvm_``SEV_(ID_, $sformatf("%s[%0d] item uncompared:\n%s", `"Q_`", i, item.sprint())) \
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
      `uvm_``SEV_(ID_, $sformatf("%s item uncompared:\n%s", `"MAILBOX_`", item.sprint())) \
    end \
  end
`endif

// get parity - implemented as a macro so that it can be invoked in constraints as well
`ifndef GET_PARITY
  `define GET_PARITY(val, odd=0) (^val ^ odd)
`endif

// wait a task or statement with timer watchdog
// input WAIT_ need to be a statement. Here are some examples
// `DV_SPINWAIT(wait(...);, "Wait for ...")
// `DV_SPINWAIT(
//              while (1) begin
//                ...
//              end)
`ifndef DV_SPINWAIT
`define DV_SPINWAIT(WAIT_, MSG_ = "timeout occurred!", TIMEOUT_NS_ = default_spinwait_timeout_ns, ID_ =`gfn) \
  begin \
    fork begin \
      fork \
        begin \
          WAIT_ \
        end \
        begin \
          wait_timeout(TIMEOUT_NS_, ID_, MSG_); \
        end \
      join_any \
      disable fork; \
    end join \
  end
`endif
