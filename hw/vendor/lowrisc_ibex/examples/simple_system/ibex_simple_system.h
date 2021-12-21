// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "verilated_toplevel.h"
#include "verilator_memutil.h"

class SimpleSystem {
 public:
  SimpleSystem(const char *ram_hier_path, int ram_size_words);
  virtual ~SimpleSystem() {}
  virtual int Main(int argc, char **argv);

 protected:
  ibex_simple_system _top;
  VerilatorMemUtil _memutil;
  MemArea _ram;

  virtual int Setup(int argc, char **argv, bool &exit_app);
  virtual void Run();
  virtual bool Finish();
};
