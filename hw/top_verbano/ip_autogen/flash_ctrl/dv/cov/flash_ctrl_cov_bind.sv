// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds FLASH_CTRL functional coverage interface to the top level FLASH_CTRL module.
`define FLASH_COV_LC_TX_BIND(__name)                     \
  bind flash_ctrl cip_lc_tx_cov_if u_``__name``_cov_if(  \
    .rst_ni (rst_ni),                                    \
    .val    (``__name``_i)                               \
 );

module flash_ctrl_cov_bind;

  `FLASH_COV_LC_TX_BIND(lc_creator_seed_sw_rw_en)
  `FLASH_COV_LC_TX_BIND(lc_owner_seed_sw_rw_en)
  `FLASH_COV_LC_TX_BIND(lc_iso_part_sw_rd_en)
  `FLASH_COV_LC_TX_BIND(lc_iso_part_sw_wr_en)
  `FLASH_COV_LC_TX_BIND(lc_seed_hw_rd_en)
  `FLASH_COV_LC_TX_BIND(lc_escalate_en)
  `FLASH_COV_LC_TX_BIND(lc_nvm_debug_en)

  bind prim_generic_flash_bank flash_ctrl_phy_cov_if u_phy_cov_if
  (
     .clk_i(clk_i),
     .rst_ni(rst_ni),
     .rd_buf_en(tb.dut.u_flash_hw_if.rd_buf_en_o),
     .rd_req(rd_i),
     .prog_req(prog_i),
     .pg_erase_req(pg_erase_i),
     .bk_erase_req(bk_erase_i),
     .ack(ack_o),
     .addr(addr_i)
  );

endmodule
