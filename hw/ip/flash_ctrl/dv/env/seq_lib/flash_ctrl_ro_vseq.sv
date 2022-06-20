// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Send read only traffic
// No protection is applied.
// TB memory model is disabled.
class flash_ctrl_ro_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_ro_vseq)
  `uvm_object_new

  virtual task body();
    flash_op_t ctrl, host;
    int num, bank;
    int host_num, host_bank;
    data_4s_t rdata;
    bit [OTFHostId:0] end_addr;
    ctrl.partition  = FlashPartData;
    cfg.clk_rst_vif.wait_clks(5);

    fork
      begin
        repeat(100) begin
          host.otf_addr[OTFHostId-1:0] = $urandom();
          host.otf_addr[1:0] = 'h0;
          host_num = $urandom_range(1,128);
          host_bank = $urandom_range(0,1);
          otf_direct_read(host.otf_addr, host_bank, host_num);
        end
        csr_utils_pkg::wait_no_outstanding_access();
      end
      begin
        repeat(100) begin
          num = $urandom_range(CTRL_TRANS_MIN, CTRL_TRANS_MAX);
          bank = $urandom_range(0, 1);
          read_flash(ctrl, bank, num);
        end
      end
    join

  endtask

endclass // flash_ctrl_ro_vseq
