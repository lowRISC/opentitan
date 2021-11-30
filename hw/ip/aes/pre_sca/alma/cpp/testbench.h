// Copyright lowRISC contributors.
// Copyright IAIK.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_IP_AES_PRE_SCA_ALMA_CPP_TESTBENCH_H_
#define OPENTITAN_HW_IP_AES_PRE_SCA_ALMA_CPP_TESTBENCH_H_

#include "verilated.h"
#include "verilated_vcd_c.h"

template <class Module>
struct Testbench {
  unsigned long m_tickcount;
  Module m_core;
  VerilatedVcdC *m_trace = NULL;

  Testbench() {
    Verilated::traceEverOn(true);
    m_tickcount = 0ul;
  }

  ~Testbench() { closetrace(); }

  void opentrace(const char *vcdname) {
    if (!m_trace) {
      m_trace = new VerilatedVcdC;
      m_core.trace(m_trace, 99);
      m_trace->open(vcdname);
    }
  }

  void closetrace() {
    if (m_trace) {
      m_trace->close();
      delete m_trace;
      m_trace = NULL;
    }
  }

  void reset() {
    m_core.rst_ni = 0;
    this->tick();
    this->tick();
    m_core.rst_ni = 1;
  }

  void tick() {
    // Falling edge
    m_core.clk_i = 0;
    m_core.eval();
    if (m_trace)
      m_trace->dump(20 * m_tickcount);

    // Rising edge
    m_core.clk_i = 1;
    m_core.eval();
    if (m_trace)
      m_trace->dump(20 * m_tickcount + 10);

    // Falling edge settle eval
    m_core.clk_i = 0;
    m_core.eval();

    if (m_trace)
      m_trace->flush();
    m_tickcount++;
  }

  bool done() { return Verilated::gotFinish(); }
};

#endif  // OPENTITAN_HW_IP_AES_PRE_SCA_ALMA_CPP_TESTBENCH_H_
