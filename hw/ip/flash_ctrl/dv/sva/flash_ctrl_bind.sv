// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module flash_ctrl_bind;

  bind flash_ctrl tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (core_tl_i),
    .d2h  (core_tl_o)
  );

  bind flash_ctrl flash_ctrl_core_csr_assert_fpv flash_ctrl_core_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (core_tl_i),
    .d2h    (core_tl_o)
  );

  if (`PRIM_DEFAULT_IMPL == prim_pkg::ImplGeneric) begin : gen_mif_bind
    for (genvar i = 0; i < flash_ctrl_pkg::NumBanks; i++) begin : gen_per_bank
      bind tb.dut.u_eflash.u_flash.gen_generic.u_impl_generic.gen_prim_flash_banks[i].
                    u_prim_flash_bank flash_ctrl_mem_if flash_ctrl_mem_if (
        .clk_i,
        .rst_ni,
        .data_mem_req,
        .mem_wr,
        .mem_addr,
        .mem_wdata,
        .mem_part,
        .mem_info_sel,
        .info0_mem_req (gen_info_types[0].info_mem_req),
        .info1_mem_req (gen_info_types[1].info_mem_req),
        .info2_mem_req (gen_info_types[2].info_mem_req)
      );
    end
  end
endmodule
