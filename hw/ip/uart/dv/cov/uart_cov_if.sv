// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for UART.
interface uart_cov_if (
  input logic clk_i
);

  import uvm_pkg::*;
  import dv_utils_pkg::*;
  `include "dv_fcov_macros.svh"

  bit en_full_cov = 1'b1;
  bit en_intg_cov = 1'b1;

  // If en_full_cov is set, then en_intg_cov must also be set since it is a subset.
  bit en_intg_cov_loc;
  assign en_intg_cov_loc = en_full_cov | en_intg_cov;

  // References to cov interfaces bound to sub-modules need to be held inside a class.
  class uart_cov_vifs_wrap extends dv_vif_wrap;
    virtual uart_core_cov_if uart_core_cov_vif;

    function new(string hier, string name);
      super.new(hier, name);
    endfunction

    // The section below constructs the `get_vifs()` task using the helper macros. It retrieves the
    // VIF handles bound to sub-modules from the uvm_resource_db.
    `DV_VIF_WRAP_GET_VIFS_BEGIN
      `DV_VIF_WRAP_GET_VIF(uart_core_cov_if, uart_core_cov_vif)
    `DV_VIF_WRAP_GET_VIFS_END

  endclass

  uart_cov_vifs_wrap m_uart_cov_vifs_wrap;

  initial begin
    m_uart_cov_vifs_wrap = new(dv_utils_pkg::get_parent_hier(.hier($sformatf("%m"))),
                               "m_uart_cov_vifs_wrap");
    m_uart_cov_vifs_wrap.get_vifs();
  end

  covergroup uart_op_cg @(posedge clk_i);
    option.name         = "uart_op_cg";
    option.comment      = "UART TX and RX operations";
    option.per_instance = 1;

    cp_tx_enable:     coverpoint uart_core.tx_enable;
    cp_rx_enable:     coverpoint m_uart_cov_vifs_wrap.uart_core_cov_vif.rx_enable;
    cr_tx_rx_enable:  cross cp_tx_enable, cp_rx_enable;
  endgroup
  `DV_FCOV_INSTANTIATE_CG(uart_op_cg, en_full_cov)

endinterface
