// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <algorithm>
#include <iostream>
#include <string>
#include <vector>

#include "verilated_toplevel.h"
#include "verilator_memutil.h"
#include "verilator_sim_ctrl.h"

int main(int argc, char **argv) {
  chip_sim_tb top;
  VerilatorMemUtil memutil;
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.clk_i, &top.rst_ni,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  std::string top_scope("TOP.chip_sim_tb.u_dut.top_darjeeling");
  std::string ram1p_adv_scope(
      "gen_ram_inst[0].u_mem.gen_generic.u_impl_generic");

  MemArea rom(top_scope + (".u_rom_ctrl0.gen_rom_scramble_enabled.u_rom.u_rom."
                           "u_prim_rom.gen_generic.u_impl_generic"),
              0x4000 / 4, 4);
  MemArea ram(top_scope +
                  ".u_sram_ctrl_main.u_prim_ram_1p_scr.u_prim_ram_1p_adv." +
                  ram1p_adv_scope,
              0x20000 / 4, 4);

  // TODO: The CTN SRAM presently does not employ scrambling.
  MemArea ctn_ram(
      "TOP.chip_sim_tb.u_dut.u_prim_ram_1p_adv_ctn." + ram1p_adv_scope,
      0x100000 / 4, 4);

  MemArea otp(top_scope + ".u_otp_macro.u_prim_ram_1p_adv." + ram1p_adv_scope,
              0x4000 / 4, 4);

  memutil.RegisterMemoryArea("rom", 0x8000, &rom);
  memutil.RegisterMemoryArea("ram", 0x10000000u, &ram);
  memutil.RegisterMemoryArea("ctn_ram", 0x41000000u, &ctn_ram);
  memutil.RegisterMemoryArea("otp", 0x80000000u /* (bogus LMA) */, &otp);
  simctrl.RegisterExtension(&memutil);

  // The initial reset delay must be long enough such that pwr/rst/clkmgr will
  // release clocks to the entire design.  This allows for synchronous resets
  // to appropriately propagate.
  // The reset duration must be appropriately sized to the divider for clk_aon
  // in chip_darjeeling_verilator.sv.  It must be at least 2 cycles of clk_aon.
  simctrl.SetInitialResetDelay(20000);
  simctrl.SetResetDuration(10);

  std::cout << "Simulation of OpenTitan Darjeeling" << std::endl
            << "==================================" << std::endl
            << std::endl;

  return simctrl.Exec(argc, argv).first;
}
