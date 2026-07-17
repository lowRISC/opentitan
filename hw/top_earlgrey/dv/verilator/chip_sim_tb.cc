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

  // Suffix this (_pd_main) once paths to IPs in the Aon power domain are needed
  std::string top_scope("TOP.chip_sim_tb.u_dut.top_earlgrey.earlgrey_pd_main");
  std::string ram1p_adv_scope("u_prim_ram_1p_adv.gen_ram_inst[0].u_mem");

  MemArea rom0(top_scope + (".u_rom_ctrl.gen_rom_scramble_enabled.u_rom.u_rom."
                            "u_prim_rom"),
               0x30000 / 4, 4);
  MemArea ram(top_scope + ".u_ram1p_ram_main." + ram1p_adv_scope, 0x20000 / 4,
              4);
  MemArea rram(top_scope + ".u_rram_macro.u_data_array", 0x200000 / 16, 16);

  std::vector<uint8_t> all_zeros(rram.GetSizeBytes());
  std::fill(all_zeros.begin(), all_zeros.end(), 0x00u);
  rram.Write(/*word_offset=*/0, all_zeros);

  // OTP occupies the last pages of the RRAM data array.
  // The OTP vmem file's own @addr fields are already absolute RRAM word
  // addresses (see gen-rram-img.py --out-otp-vmem).
  MemArea otp(top_scope + ".u_rram_macro.u_data_array", 0x200000 / 16, 16);

  memutil.RegisterMemoryArea("rom0", 0x40000, &rom0);
  memutil.RegisterMemoryArea("ram", 0x10000000u, &ram);
  memutil.RegisterMemoryArea("rram", 0x30000000u, &rram);
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
