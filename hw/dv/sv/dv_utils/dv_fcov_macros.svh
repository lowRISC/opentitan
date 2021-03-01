// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Include FCOV RTL by default. Exclude it for synthesis and where explicitly requested (by defining
// EXCLUDE_FCOV).
`ifdef SYNTHESIS
  `define EXCLUDE_FCOV
`elsif YOSYS
  `define EXCLUDE_FCOV
`endif

// Coverage support is not always available but it's useful to include extra fcov signals for
// linting purposes. They need to be marked as unused to avoid warnings.
`ifndef FCOV_MARK_UNUSED
  `define FCOV_MARK_UNUSED(TYPE_, NAME_) \
    TYPE_ unused_fcov_``NAME_; \
    assign unused_fcov_``NAME_ = fcov_``NAME_;
`endif

// Define a signal and expression in the design for capture in functional coverage
`ifndef FCOV_SIGNAL
`ifdef EXCLUDE_FCOV
  // Macro has no effect
  `define FCOV_SIGNAL(TYPE_, NAME_, EXPR_)
`else
  `define FCOV_SIGNAL(TYPE_, NAME_, EXPR_) \
    TYPE_ fcov_``NAME_; \
    assign fcov_``NAME_ = EXPR_; \
    `FCOV_MARK_UNUSED(TYPE_, NAME_)
`endif
`endif

// Define a signal and expression in the design for capture in functional coverage depending on
// design configuration. The input GEN_COND_ must be a constant or parameter.
`ifndef FCOV_SIGNAL_GEN_IF
`ifdef EXCLUDE_FCOV
  // Macro does nothing
  `define FCOV_SIGNAL_GEN_IF(TYPE_, NAME_, EXPR_, GEN_COND_, DEFAULT_ = '0)
`else
  `define FCOV_SIGNAL_GEN_IF(TYPE_, NAME_, EXPR_, GEN_COND_, DEFAULT_ = '0) \
    TYPE_ fcov_``NAME_; \
    if (GEN_COND_) begin : g_fcov_``NAME_ \
      assign fcov_``NAME_ = EXPR_; \
    end else begin : g_no_fcov_``NAME_ \
      assign fcov_``NAME_ = DEFAULT_; \
    end \
    `FCOV_MARK_UNUSED(TYPE_, NAME_)
`endif
`endif
