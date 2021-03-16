// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <iostream>

#include "verilated_toplevel.h"
#include "verilator_memutil.h"
#include "verilator_sim_ctrl.h"

int main(int argc, char **argv) {
  top_englishbreakfast_verilator top;
  VerilatorMemUtil memutil;
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.clk_i, &top.rst_ni,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  std::string top_scope(
      "TOP.top_englishbreakfast_verilator."
      "top_englishbreakfast");
  std::string ram1p_adv_scope(
      "u_prim_ram_1p_adv.u_mem."
      "gen_generic.u_impl_generic");

  std::string rom_scope(top_scope +
                        ".u_rom_rom.u_prim_rom.gen_generic.u_impl_generic");
  std::string ram_scope(top_scope + ".u_ram1p_ram_main." + ram1p_adv_scope);
  std::string flash_scope(top_scope +
                          ".u_flash_eflash.u_flash."
                          "gen_generic.u_impl_generic."
                          "gen_prim_flash_banks[0]."
                          "u_prim_flash_bank.u_mem."
                          "gen_generic.u_impl_generic");

  std::unique_ptr<MemArea> rom(new MemArea(rom_scope, 0x4000 / 4, 4)),
      ram(new MemArea(ram_scope, 0x20000 / 4, 4)),
      flash(new MemArea(flash_scope, 0x100000 / 8, 8));

  memutil.RegisterMemoryArea("rom", 0x8000, std::move(rom));
  memutil.RegisterMemoryArea("ram", 0x10000000u, std::move(ram));
  memutil.RegisterMemoryArea("flash", 0x20000000u, std::move(flash));
  simctrl.RegisterExtension(&memutil);

  // see top_earlgrey_verilator.cc for justification and explanation
  simctrl.SetInitialResetDelay(500);
  simctrl.SetResetDuration(10);

  std::cout << "Simulation of OpenTitan English Breakfast" << std::endl
            << "=================================" << std::endl
            << std::endl;

  return simctrl.Exec(argc, argv).first;
}
