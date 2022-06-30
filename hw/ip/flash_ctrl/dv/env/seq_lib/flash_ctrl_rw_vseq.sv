// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_rw_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_rw_vseq)
  `uvm_object_new

  virtual task body();
    flash_op_t ctrl, host;
    int bank;
    int host_num, host_bank;
    ctrl.partition = FlashPartData;
    cfg.clk_rst_vif.wait_clks(5);

    fork
      begin
        repeat(500) begin
          `DV_CHECK_RANDOMIZE_FATAL(this)
          bank = $urandom_range(0, 1);
          randcase
            1:prog_flash(ctrl, bank, ctrl_num);
            1:read_flash(ctrl, bank, ctrl_num);
          endcase
        end
      end
      begin
         for (int i = 0; i < 100; ++i) begin
	    fork
               host.otf_addr[OTFHostId-1:0] = $urandom();
               host.otf_addr[1:0] = 'h0;
               host_num = $urandom_range(1,128);
               host_bank = $urandom_range(0,1);
               otf_direct_read(host.otf_addr, host_bank, host_num);
            join_none
	    #0;
	 end
         csr_utils_pkg::wait_no_outstanding_access();
      end
    join
  endtask
endclass // flash_ctrl_rw_vseq
