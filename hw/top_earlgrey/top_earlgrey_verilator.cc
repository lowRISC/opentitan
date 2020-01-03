// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <iostream>

#include "verilated_toplevel.h"
#include "verilator_memutil.h"
#include "verilator_sim_ctrl.h"

int main(int argc, char **argv) {
  top_earlgrey_verilator top;
  VerilatorMemUtil memutil;
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.clk_i, &top.rst_ni,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  memutil.RegisterMemoryArea(
      "rom",
      "TOP.top_earlgrey_verilator.top_earlgrey.u_rom_rom.gen_mem_generic."
      "u_impl_generic");
  memutil.RegisterMemoryArea(
      "ram",
      "TOP.top_earlgrey_verilator.top_earlgrey.u_ram1p_ram_main"
      ".gen_mem_generic.u_impl_generic");
  memutil.RegisterMemoryArea(
      "flash",
      "TOP.top_earlgrey_verilator.top_earlgrey.u_flash_eflash."
      "gen_flash_banks[0].u_flash.gen_flash.u_impl_generic.u_mem.gen_mem_"
      "generic.u_impl_"
      "generic");
  simctrl.RegisterExtension(&memutil);

  std::cout << "Simulation of OpenTitan Earl Grey" << std::endl
            << "=================================" << std::endl
            << std::endl;

  return simctrl.Exec(argc, argv);
}
