// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_phy_arb_redun_vseq extends flash_ctrl_err_base_vseq;
  `uvm_object_utils(flash_ctrl_phy_arb_redun_vseq)
  `uvm_object_new

  task run_error_event();
    int delay;
    bit arb_err;
    string path = {"tb.dut.u_eflash.gen_flash_cores[0].",
                   "u_core.u_host_arb.gen_input_bufs[1].u_req_buf.out_o[1:0]"};
    cfg.scb_h.exp_alert["fatal_err"] = 1;
    cfg.scb_h.alert_chk_max_delay["fatal_err"] = 2000;
    cfg.scb_h.exp_alert_contd["fatal_err"] = 10000;

    repeat (2) begin
      // unit 100 ns;
      delay = $urandom_range(1, 10);
      #(delay * 100ns);
      if (arb_err) begin
        `DV_CHECK(uvm_hdl_release(path))
      end else begin
        arb_err = 1;
        `DV_CHECK(uvm_hdl_force(path, 2'h0))
      end
    end // repeat (2)
    check_fault(ral.fault_status.arb_err);
  endtask
endclass
