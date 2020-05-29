// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_VERILATOR_SIMUTIL_VERILATOR_CPP_VERILATED_TOPLEVEL_H_
#define OPENTITAN_HW_DV_VERILATOR_SIMUTIL_VERILATOR_CPP_VERILATED_TOPLEVEL_H_

#ifndef TOPLEVEL_NAME
#error "TOPLEVEL_NAME must be set to the name of the toplevel."
#endif

#include <verilated.h>

#define STR(s) #s
#define STR_AND_EXPAND(s) STR(s)

// Include Verilator-generated toplevel
#define VERILATED_TOPLEVEL_HEADER_STR2(s) STR(V##s)
#define VERILATED_TOPLEVEL_HEADER_STR(s) VERILATED_TOPLEVEL_HEADER_STR2(s)

#include VERILATED_TOPLEVEL_HEADER_STR(TOPLEVEL_NAME.h)

// Name of the Verilated class
#define VERILATED_TOPLEVEL_NAME3(s) V##s
#define VERILATED_TOPLEVEL_NAME2(s) VERILATED_TOPLEVEL_NAME3(s)
#define VERILATED_TOPLEVEL_NAME VERILATED_TOPLEVEL_NAME2(TOPLEVEL_NAME)

// VM_TRACE is defined by Verilator and passed through the command line as 1 or
// 0. The code below serves as safety net only.
#ifndef VM_TRACE
#define VM_TRACE 0
#endif

// VM_TRACE_FMT_FST must be set by the user when calling Verilator with
// --trace-fst. VM_TRACE is set by Verilator itself.
#if VM_TRACE == 1
#ifdef VM_TRACE_FMT_FST
#include "verilated_fst_c.h"
#define VM_TRACE_CLASS_NAME VerilatedFstC
#else
#include "verilated_vcd_c.h"
#define VM_TRACE_CLASS_NAME VerilatedVcdC
#endif
#endif

#if VM_TRACE == 1
/**
 * "Base" for all tracers in Verilator with common functionality
 *
 * This class is (like the VerilatedToplevel class) a workaround for the
 * insufficient class hierarchy in Verilator-generated C++ code.
 *
 * Once Verilator is improved to support this functionality natively this class
 * should go away.
 */
class VerilatedTracer {
 public:
  VerilatedTracer() : impl_(nullptr) { impl_ = new VM_TRACE_CLASS_NAME(); };

  ~VerilatedTracer() { delete impl_; }

  bool isOpen() const { return impl_->isOpen(); };

  void open(const char *filename) { impl_->open(filename); };

  void close() { impl_->close(); };

  void dump(vluint64_t timeui) { impl_->dump(timeui); }

  operator VM_TRACE_CLASS_NAME *() const {
    assert(impl_);
    return impl_;
  }

 private:
  VM_TRACE_CLASS_NAME *impl_;
};
#else
/**
 * No-op tracer interface
 */
class VerilatedTracer {
 public:
  VerilatedTracer(){};
  ~VerilatedTracer() {}
  bool isOpen() const { return false; };
  void open(const char *filename){};
  void close(){};
  void dump(vluint64_t timeui) {}
};
#endif  // VM_TRACE == 1

// Forward-declare for use in VerilatedToplevel
class TOPLEVEL_NAME;

/**
 * Abstract class for verilated toplevel modules
 *
 * Verilator-produced toplevel modules do not have a common base class defining
 * the methods such as eval(); instead, they are only inheriting from the
 * generic VerilatedModule class, which doesn't have toplevel-specific
 * functionality. This makes it impossible to write code which accepts any
 * toplevel module as input by specifying the common "toplevel base class".
 *
 * This class, VerilatedToplevel, fills this gap by defining an abstract base
 * class for verilated toplevel modules. This class should be used together with
 * the VERILATED_TOPLEVEL macro.
 *
 * Note that this function is a workaround until Verilator gains this
 * functionality natively.
 *
 * To support the different tracing implementations (VCD, FST or no tracing),
 * the trace() function is modified to take a VerilatedTracer argument instead
 * of the tracer-specific class.
 */
class VerilatedToplevel {
 public:
  VerilatedToplevel(){};
  virtual ~VerilatedToplevel(){};

  virtual void eval() = 0;
  virtual void final() = 0;
  virtual const char *name() const = 0;
  virtual void trace(VerilatedTracer &tfp, int levels, int options) = 0;

  /**
   * Get the Verilator-generated device under test
   *
   * Use this method to access all public signals of the DUT:
   *
   * VerilatedToplevel &top;
   * int clk_value = top->dut().IO_CLK;
   * top->dut().IO_CLK = 1;
   */
  TOPLEVEL_NAME &dut();
};

class TOPLEVEL_NAME : public VERILATED_TOPLEVEL_NAME, public VerilatedToplevel {
 public:
  TOPLEVEL_NAME(const char *name = "TOP")
      : VERILATED_TOPLEVEL_NAME(name), VerilatedToplevel() {}
  const char *name() const { return STR_AND_EXPAND(TOPLEVEL_NAME); }
  void eval() { VERILATED_TOPLEVEL_NAME::eval(); }
  void final() { VERILATED_TOPLEVEL_NAME::final(); }
  void trace(VerilatedTracer &tfp, int levels, int options = 0) {
#if VM_TRACE == 1
    VERILATED_TOPLEVEL_NAME::trace(static_cast<VM_TRACE_CLASS_NAME *>(tfp),
                                   levels, options);
#else
    assert(0 && "Tracing not enabled.");
#endif
  }
};

#endif  // OPENTITAN_HW_DV_VERILATOR_SIMUTIL_VERILATOR_CPP_VERILATED_TOPLEVEL_H_
