// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <fstream>
#include <iostream>

#include "ibex_pcounts.h"
#include "verilated_toplevel.h"
#include "verilator_memutil.h"
#include "verilator_sim_ctrl.h"

int main(int argc, char **argv) {
  ibex_simple_system top;
  VerilatorMemUtil memutil;
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.IO_CLK, &top.IO_RST_N,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  memutil.RegisterMemoryArea(
      "ram", "TOP.ibex_simple_system.u_ram.u_ram.gen_generic.u_impl_generic");
  simctrl.RegisterExtension(&memutil);

  std::cout << "Simulation of Ibex" << std::endl
            << "==================" << std::endl
            << std::endl;

  if (simctrl.Exec(argc, argv)) {
    return 1;
  }

  // Set the scope to the root scope, the ibex_pcount_string function otherwise
  // doesn't know the scope itself. Could be moved to ibex_pcount_string, but
  // would require a way to set the scope name from here, similar to MemUtil.
  svSetScope(svGetScopeFromName("TOP.ibex_simple_system"));
  // TODO: Exec can return with "true" (e.g. with `-h`), but that does not mean
  // `RunSimulation()` was executed. The folllowing values will not be useful
  // in this case.
  std::cout << "\nPerformance Counters" << std::endl
            << "====================" << std::endl;
  std::cout << ibex_pcount_string(false);

  std::ofstream pcount_csv("ibex_simple_system_pcount.csv");
  pcount_csv << ibex_pcount_string(true);

  return 0;
}
