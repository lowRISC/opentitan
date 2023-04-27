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

  std::string top_scope("TOP.chip_sim_tb.u_dut.top_earlgrey");
  std::string ram1p_adv_scope(
      "u_prim_ram_1p_adv.u_mem."
      "gen_generic.u_impl_generic");

  MemArea rom(top_scope + (".u_rom_ctrl.gen_rom_scramble_enabled.u_rom.u_rom."
                           "u_prim_rom.gen_generic.u_impl_generic"),
              0x4000 / 4, 4);
  MemArea ram(top_scope + ".u_ram1p_ram_main." + ram1p_adv_scope, 0x20000 / 4,
              4);
  // Only handle the lower bank of flash for now.
  MemArea flash0(
      top_scope +
          ".u_flash_ctrl.u_eflash.u_flash.gen_generic.u_impl_generic."
          "gen_prim_flash_banks[0].u_prim_flash_bank.u_mem."
          "gen_generic.u_impl_generic",
      0x80000 / 8, 8);
  MemArea flash1(
      top_scope +
          ".u_flash_ctrl.u_eflash.u_flash.gen_generic.u_impl_generic."
          "gen_prim_flash_banks[1].u_prim_flash_bank.u_mem."
          "gen_generic.u_impl_generic",
      0x80000 / 8, 8);
  // Start with the flash region erased. Future loads can overwrite.
  std::vector<uint8_t> all_ones(flash0.GetSizeBytes());
  std::fill(all_ones.begin(), all_ones.end(), 0xffu);
  flash0.Write(/*word_offset=*/0, all_ones);
  flash1.Write(/*word_offset=*/0, all_ones);

  MemArea otp(top_scope + ".u_otp_ctrl.u_otp.gen_generic.u_impl_generic." +
                  ram1p_adv_scope,
              0x4000 / 4, 4);

  memutil.RegisterMemoryArea("rom", 0x8000, &rom);
  memutil.RegisterMemoryArea("ram", 0x10000000u, &ram);
  memutil.RegisterMemoryArea("flash0", 0x20000000u, &flash0);
  memutil.RegisterMemoryArea("flash1", 0x20080000u, &flash1);
  memutil.RegisterMemoryArea("otp", 0x40000000u /* (bogus LMA) */, &otp);
  simctrl.RegisterExtension(&memutil);

  // The initial reset delay must be long enough such that pwr/rst/clkmgr will
  // release clocks to the entire design.  This allows for synchronous resets
  // to appropriately propagate.
  // The reset duration must be appropriately sized to the divider for clk_aon
  // in chip_earlgrey_verilator.sv.  It must be at least 2 cycles of clk_aon.
  simctrl.SetInitialResetDelay(20000);
  simctrl.SetResetDuration(10);

  std::cout << "Simulation of OpenTitan Earl Grey" << std::endl
            << "=================================" << std::endl
            << std::endl;

  return simctrl.Exec(argc, argv).first;
}
