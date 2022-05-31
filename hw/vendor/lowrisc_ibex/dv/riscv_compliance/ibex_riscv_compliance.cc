// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "verilated_toplevel.h"
#include "verilator_memutil.h"
#include "verilator_sim_ctrl.h"

int main(int argc, char **argv) {
  ibex_riscv_compliance top;
  VerilatorMemUtil memutil;
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();
  simctrl.SetTop(&top, &top.IO_CLK, &top.IO_RST_N,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  MemArea ram(
      "TOP.ibex_riscv_compliance.u_ram.u_ram.gen_generic.u_impl_generic",
      64 * 1024 / 4, 4);

  memutil.RegisterMemoryArea("ram", 0x0, &ram);
  simctrl.RegisterExtension(&memutil);

  return simctrl.Exec(argc, argv).first;
}
