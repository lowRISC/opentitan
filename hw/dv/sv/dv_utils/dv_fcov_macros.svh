// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Include FCOV RTL by default. Disable it for synthesis and where explicitly requested (by defining
// DV_FCOV_DISABLE).
`ifdef SYNTHESIS
  `define DV_FCOV_DISABLE
`elsif YOSYS
  `define DV_FCOV_DISABLE
`endif

// Disable instantiations of FCOV coverpoints or covergroups.
`ifdef VERILATOR
  `define DV_FCOV_DISABLE_CP
`elsif DV_FCOV_DISABLE
  `define DV_FCOV_DISABLE_CP
`endif

// Instantiates a covergroup in an interface or module.
//
// This macro assumes that a covergroup of the same name as the NAME_ arg is defined in the
// interface or module. It just adds some extra signals and logic to control the creation of the
// covergroup instance with ~bit en_<cg_name>~. This defaults to 0. It is ORed with the external
// COND_ signal. The testbench can modify it at t = 0 based on the test being run.
// NOTE: This is not meant to be invoked inside a class.
//
// NAME_ : Name of the covergroup.
// COND_ : External condition / expr that controls the creation of the covergroup.
// ARGS_ : Arguments to covergroup instance, if any. Args MUST BE wrapped in (..).
`ifndef DV_FCOV_INSTANTIATE_CG
`ifdef DV_FCOV_DISABLE_CP
  `define DV_FCOV_INSTANTIATE_CG(NAME_, COND_ = 1'b1, ARGS_ = ())
`else
  `define DV_FCOV_INSTANTIATE_CG(NAME_, COND_ = 1'b1, ARGS_ = ()) \
    bit en_``NAME_ = 1'b0; \
    NAME_ NAME_``_inst; \
    initial begin \
      /* The #1 delay below allows any part of the tb to control the conditions first at t = 0. */ \
      #1; \
      if ((en_``NAME_) || (COND_)) begin \
        $display("%0t: (%0s:%0d) [%m] %0s", $time, `__FILE__, `__LINE__, \
                 {"Creating covergroup ", `"NAME_`"}); \
        NAME_``_inst = new``ARGS_; \
      end \
    end
`endif
`endif

// Creates a coverpoint for an expression where only the expression true case is of interest for
// coverage (e.g. where the expression indicates an event has occured).
`ifndef DV_FCOV_EXPR_SEEN
`ifdef DV_FCOV_DISABLE_CP
  `define DV_FCOV_EXPR_SEEN(NAME_, EXPR_)
`else
  `define DV_FCOV_EXPR_SEEN(NAME_, EXPR_) cp_``NAME_: coverpoint EXPR_ { bins seen = {1}; }
`endif
`endif

// Creates a SVA cover that can be used in a covergroup.
//
// This macro creates an unnamed SVA cover from the property (or an expression) `PROP_` and an event
// with the name `EV_NAME_`. When the SVA cover is hit, the event is triggered. A coverpoint can
// cover the `triggered` property of the event.
`ifndef DV_FCOV_SVA
`ifdef DV_FCOV_DISABLE
  `define DV_FCOV_SVA(EV_NAME_, PROP_, CLK_ = clk_i, RST_ = rst_ni)
`else
  `define DV_FCOV_SVA(EV_NAME_, PROP_, CLK_ = clk_i, RST_ = rst_ni) \
    event EV_NAME_; \
    cover property (@(posedge CLK_) disable iff (RST_ == 0) (PROP_)) begin \
      -> EV_NAME_; \
    end
`endif
`endif

// Coverage support is not always available but it's useful to include extra fcov signals for
// linting purposes. They need to be marked as unused to avoid warnings.
`ifndef DV_FCOV_MARK_UNUSED
  `define DV_FCOV_MARK_UNUSED(TYPE_, NAME_) \
    TYPE_ unused_fcov_``NAME_; \
    assign unused_fcov_``NAME_ = fcov_``NAME_;
`endif

// Define a signal and expression in the design for capture in functional coverage
`ifndef DV_FCOV_SIGNAL
`ifdef DV_FCOV_DISABLE
  `define DV_FCOV_SIGNAL(TYPE_, NAME_, EXPR_)
`else
  `define DV_FCOV_SIGNAL(TYPE_, NAME_, EXPR_) \
    TYPE_ fcov_``NAME_; \
    assign fcov_``NAME_ = EXPR_; \
    `DV_FCOV_MARK_UNUSED(TYPE_, NAME_)
`endif
`endif

// Define a signal and expression in the design for capture in functional coverage depending on
// design configuration. The input GEN_COND_ must be a constant or parameter.
`ifndef DV_FCOV_SIGNAL_GEN_IF
`ifdef DV_FCOV_DISABLE
  `define DV_FCOV_SIGNAL_GEN_IF(TYPE_, NAME_, EXPR_, GEN_COND_, DEFAULT_ = '0)
`else
  `define DV_FCOV_SIGNAL_GEN_IF(TYPE_, NAME_, EXPR_, GEN_COND_, DEFAULT_ = '0) \
    TYPE_ fcov_``NAME_; \
    if (GEN_COND_) begin : g_fcov_``NAME_ \
      assign fcov_``NAME_ = EXPR_; \
    end else begin : g_no_fcov_``NAME_ \
      assign fcov_``NAME_ = DEFAULT_; \
    end \
    `DV_FCOV_MARK_UNUSED(TYPE_, NAME_)
`endif
`endif
