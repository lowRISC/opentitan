// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macro bodies included by prim_assert.sv for tools that support full SystemVerilog and SVA syntax.
// See prim_assert.sv for documentation for each of the macros.
//
// Each macro body is individually guarded by `ifdef OCAH_OT_INC_ASSERT (defined in prim_assert.sv).
// When OCAH_OT_INC_ASSERT is not defined (e.g. under SYNTHESIS or VERILATOR) the macros expand to
// nothing. This mirrors the PULP common_cells assertion style of wrapping the macro bodies in place
// rather than swapping in a separate set of dummy (empty) macro definitions.

`define OCAH_OT_ASSERT_I(__name, __prop) \
`ifdef OCAH_OT_INC_ASSERT                \
  __name: assert (__prop)                \
    else begin                           \
      `OCAH_OT_ASSERT_ERROR(__name)      \
    end                                  \
`endif

// Formal tools will ignore the initial construct, so use static assertion as a workaround.
// This workaround terminates design elaboration if the __prop predict is false.
// It calls $fatal() with the first argument equal to 2, it outputs the statistics about the memory
// and CPU time.
`define OCAH_OT_ASSERT_INIT(__name, __prop)                                          \
`ifdef OCAH_OT_INC_ASSERT                                                            \
`ifdef FPV_ON                                                                        \
  if (!(__prop)) $fatal(2, "Fatal static assertion [%s]: (%s) is not true.",         \
                        (__name), (__prop));                                         \
`else                                                                                \
  initial begin                                                                      \
    __name: assert (__prop)                                                          \
      else begin                                                                     \
        `OCAH_OT_ASSERT_ERROR(__name)                                                \
      end                                                                            \
  end                                                                                \
`endif                                                                               \
`endif

`define OCAH_OT_ASSERT_INIT_NET(__name, __prop)                                      \
`ifdef OCAH_OT_INC_ASSERT                                                            \
  initial begin                                                                      \
    // When a net is assigned with a value, the assignment is evaluated after        \
    // initial in Xcelium. Add 1ps delay to check value after the assignment is      \
    // completed.                                                                    \
    #1ps;                                                                            \
    __name: assert (__prop)                                                          \
      else begin                                                                     \
        `OCAH_OT_ASSERT_ERROR(__name)                                                \
      end                                                                            \
  end                                                                                \
`endif

`define OCAH_OT_ASSERT_FINAL(__name, __prop)                                 \
`ifdef OCAH_OT_INC_ASSERT                                                    \
`ifndef FPV_ON                                                               \
  final begin                                                                \
    __name: assert (__prop || $test$plusargs("disable_assert_final_checks")) \
      else begin                                                             \
        `OCAH_OT_ASSERT_ERROR(__name)                                        \
      end                                                                    \
  end                                                                        \
`endif                                                                       \
`endif

`define OCAH_OT_ASSERT_AT_RESET(__name, __prop, __rst = `OCAH_OT_ASSERT_DEFAULT_RST) \
`ifdef OCAH_OT_INC_ASSERT                                                     \
  // `__rst` is active-high for these macros, so trigger on its posedge.      \
  // The values inside the property are sampled just before the trigger,      \
  // which is necessary to make the evaluation of `__prop` on a reset edge    \
  // meaningful.  On any reset posedge at the start of time, `__rst` itself   \
  // is unknown, and at that time `__prop` is likely not initialized either,  \
  // so this assertion does not evaluate `__prop` when `__rst` is unknown.    \
  //                                                                          \
  // This extra behaviour is not used for FPV, because Jasper doesn't support \
  // it and instead prints the WNL038 warning. Avoid the check and warning    \
  // message in this case.                                                    \
`ifndef FPV_ON                                                                \
  __name: assert property (@(posedge __rst) $isunknown(__rst) || (__prop))    \
`else                                                                         \
  __name: assert property (@(posedge __rst) (__prop))                         \
`endif                                                                        \
    else begin                                                                \
      `OCAH_OT_ASSERT_ERROR(__name)                                           \
    end                                                                       \
`endif

`define OCAH_OT_ASSERT_AT_RESET_AND_FINAL(__name, __prop, __rst = `OCAH_OT_ASSERT_DEFAULT_RST) \
    `OCAH_OT_ASSERT_AT_RESET(AtReset_``__name``, __prop, __rst)                        \
    `OCAH_OT_ASSERT_FINAL(Final_``__name``, __prop)

`define OCAH_OT_ASSERT(__name, __prop, __clk = `OCAH_OT_ASSERT_DEFAULT_CLK, __rst = `OCAH_OT_ASSERT_DEFAULT_RST) \
`ifdef OCAH_OT_INC_ASSERT                                                                \
  __name: assert property (@(posedge __clk) disable iff ((__rst) !== '0) (__prop))       \
    else begin                                                                           \
      `OCAH_OT_ASSERT_ERROR(__name)                                                      \
    end                                                                                  \
`endif

`define OCAH_OT_ASSERT_NEVER(__name, __prop, __clk = `OCAH_OT_ASSERT_DEFAULT_CLK, __rst = `OCAH_OT_ASSERT_DEFAULT_RST) \
`ifdef OCAH_OT_INC_ASSERT                                                                      \
  __name: assert property (@(posedge __clk) disable iff ((__rst) !== '0) not (__prop))         \
    else begin                                                                                 \
      `OCAH_OT_ASSERT_ERROR(__name)                                                            \
    end                                                                                        \
`endif

`define OCAH_OT_ASSERT_KNOWN(__name, __sig, __clk = `OCAH_OT_ASSERT_DEFAULT_CLK, __rst = `OCAH_OT_ASSERT_DEFAULT_RST) \
`ifdef OCAH_OT_INC_ASSERT                                                                     \
`ifndef FPV_ON                                                                                \
  `OCAH_OT_ASSERT(__name, !$isunknown(__sig), __clk, __rst)                                   \
`endif                                                                                        \
`endif

`define OCAH_OT_COVER(__name, __prop, __clk = `OCAH_OT_ASSERT_DEFAULT_CLK, __rst = `OCAH_OT_ASSERT_DEFAULT_RST) \
`ifdef OCAH_OT_INC_ASSERT                                                                 \
  __name: cover property (@(posedge __clk) disable iff ((__rst) !== '0) (__prop));        \
`endif

`define OCAH_OT_ASSUME(__name, __prop, __clk = `OCAH_OT_ASSERT_DEFAULT_CLK, __rst = `OCAH_OT_ASSERT_DEFAULT_RST) \
`ifdef OCAH_OT_INC_ASSERT                                                                \
  __name: assume property (@(posedge __clk) disable iff ((__rst) !== '0) (__prop))       \
    else begin                                                                           \
      `OCAH_OT_ASSERT_ERROR(__name)                                                      \
    end                                                                                  \
`endif

`define OCAH_OT_ASSUME_I(__name, __prop) \
`ifdef OCAH_OT_INC_ASSERT                \
  __name: assume (__prop)                \
    else begin                           \
      `OCAH_OT_ASSERT_ERROR(__name)      \
    end                                  \
`endif
