// Copyright lowRISC contributors.
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
      "u_prim_ram_1p_adv.u_mem."
      "gen_generic.u_impl_generic");

  MemArea rom0(top_scope + (".u_rom_ctrl0.gen_rom_scramble_enabled."
                            "u_rom.u_rom."
                            "u_prim_rom.gen_generic.u_impl_generic"),
               0x8000 / 4, 4);
  MemArea rom1(top_scope + (".u_rom_ctrl1.gen_rom_scramble_enabled."
                            "u_rom.u_rom."
                            "u_prim_rom.gen_generic.u_impl_generic"),
               0x10000 / 4, 4);
  MemArea ram(top_scope + ".u_ram1p_ram_main." + ram1p_adv_scope, 0x20000 / 4,
              4);
  Ecc32MemArea ram_ctn(
      "TOP.chip_sim_tb.u_dut.u_prim_ram_1p_adv_ctn.u_mem."
      "gen_generic.u_impl_generic",
      0x100000 / 4, 4);

  MemArea otp(top_scope + ".u_otp_ctrl.u_otp.gen_generic.u_impl_generic." +
                  ram1p_adv_scope,
              0x10000 / 4, 4);

  memutil.RegisterMemoryArea("rom", 0x8000u, &rom0);
  memutil.RegisterMemoryArea("rom1", 0x20000u, &rom1);
  memutil.RegisterMemoryArea("ram", 0x10000000u, &ram);
  memutil.RegisterMemoryArea("otp", 0x30000000u /* (bogus LMA) */, &otp);
  memutil.RegisterMemoryArea("ram_ctn", 0x41000000u, &ram_ctn);
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
