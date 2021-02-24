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
      "TOP.top_earlgrey_verilator.top_earlgrey.u_rom_rom.u_prim_rom."
      "gen_generic.u_impl_generic");
  memutil.RegisterMemoryArea(
      "ram",
      "TOP.top_earlgrey_verilator.top_earlgrey.u_ram1p_ram_main."
      "u_prim_ram_1p_adv.u_mem.gen_generic.u_impl_generic");
  memutil.RegisterMemoryArea(
      "flash",
      ("TOP.top_earlgrey_verilator.top_earlgrey.u_flash_eflash.u_flash."
       "gen_generic.u_impl_generic.gen_prim_flash_banks[0].u_prim_flash_bank.u_"
       "mem.gen_"
       "generic.u_impl_generic"),
      64, nullptr);
  memutil.RegisterMemoryArea(
      "otp",
      "TOP.top_earlgrey_verilator.top_earlgrey.u_otp_ctrl.u_otp."
      "gen_generic.u_impl_generic.u_prim_ram_1p_adv.u_mem.gen_generic."
      "u_impl_generic");
  simctrl.RegisterExtension(&memutil);
  // The initial reset delay must be long enough such that pwr/rst/clkmgr will
  // release clocks to the entire design.  This allows for synchronous resets
  // to appropriately propagate.
  // The reset duration must be appropriately sized to the divider for clk_aon
  // in top_earlgrey_verilator.sv.  It must be at least 2 cycles of clk_aon.
  simctrl.SetInitialResetDelay(500);
  simctrl.SetResetDuration(10);

  std::cout << "Simulation of OpenTitan Earl Grey" << std::endl
            << "=================================" << std::endl
            << std::endl;

  return simctrl.Exec(argc, argv).first;
}
