// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test sends 'host read' over 'slow' and 'fast' return data path.
// 'slow' and 'fast' return data path is created by
// enabling and disabling scramble for each region.
// In this test, scramble is enabled all pages in bank 0 while
// scramble is disabled in all pages in bank 1.
// Data from bank 1 return earlier than bank 0 but that should
// be re-arranged in request order at the end of read data pipe line.

class flash_ctrl_rd_ooo_vseq extends flash_ctrl_legacy_base_vseq;
  `uvm_object_utils(flash_ctrl_rd_ooo_vseq)
  `uvm_object_new

  virtual task body();
    flash_op_t ctrl;
    int num, bank;

    flash_program_data_c.constraint_mode(0);
    cfg.clk_rst_vif.wait_clks(5);
    fork
      begin
        for (int i = 0; i < cfg.otf_num_hr; ++i) begin
          fork
            send_host_rd(i);
          join_none
          #0;
        end
        csr_utils_pkg::wait_no_outstanding_access();
      end
      begin
        repeat(cfg.otf_num_rw) begin
          `DV_CHECK_RANDOMIZE_FATAL(this)
          ctrl = rand_op;
          bank = rand_op.addr[OTFBankId];
          if (ctrl.partition == FlashPartData) begin
            num = ctrl_num;
          end else begin
            num = ctrl_info_num;
          end
          read_flash(ctrl, bank, num, fractions);
        end
      end
    join
  endtask

  task send_host_rd(int idx);
    flash_op_t host;
    int host_num, host_bank;

    host.otf_addr[OTFHostId-2:0] = $urandom();
    host.otf_addr[1:0] = 'h0;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(host_num,
                                       host_num dist {1 := 5,
                                                      [2:4] := 1};)
    host_bank = $urandom_range(0,1);

    otf_direct_read(host.otf_addr, host_bank, host_num, 0);
  endtask

  task flash_otf_region_cfg(otf_cfg_mode_e scr_mode = OTFCfgFalse,
                            otf_cfg_mode_e ecc_mode = OTFCfgFalse);

    // Make default config scramble disable, ecc enable.
    flash_ctrl_default_region_cfg(.scramble_en(MuBi4False),
                                  .ecc_en(MuBi4True));
    // Scramble enable in Bank 0 only
    foreach (cfg.mp_regions[i]) begin
      cfg.mp_regions[i] = rand_regions[i];
      if (i < 2) cfg.mp_regions[i].en = MuBi4True;
      else cfg.mp_regions[i].en = MuBi4False;
      if (i == 0) begin
        cfg.mp_regions[i].scramble_en = MuBi4True;
        cfg.mp_regions[i].start_page = 0;
        cfg.mp_regions[i].num_pages = 256;
      end
      if (i == 1) begin
        cfg.mp_regions[i].scramble_en = MuBi4False;
        cfg.mp_regions[i].start_page = 256;
        cfg.mp_regions[i].num_pages = 256;
      end
      cfg.mp_regions[i].ecc_en = MuBi4True;
      flash_ctrl_mp_region_cfg(i, cfg.mp_regions[i]);
      `uvm_info("otf_region_cfg", $sformatf("region[%0d] = %p", i, cfg.mp_regions[i]), UVM_MEDIUM)
    end
    `uvm_info("otf_region_cfg", $sformatf("default = %p", cfg.default_region_cfg), UVM_MEDIUM)
    flash_ctrl_default_info_cfg(scr_mode, ecc_mode);
    update_p2r_map(cfg.mp_regions);
  endtask // flash_otf_region_cfg
  task post_start();
    flash_init = otf_flash_init;
    super.post_start();
  endtask
endclass // flash_ctrl_rd_ooo_vseq
