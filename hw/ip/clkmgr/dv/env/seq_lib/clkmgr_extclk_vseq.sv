// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The extclk vseq causes the external clock selection to be triggered. More details
// in the clkmgr_testplan.hjson file.
class clkmgr_extclk_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_extclk_vseq)

  `uvm_object_new

  // When extclk_ctrl_regwen is clear it is not possible to select external clocks.
  // This is tested in regular csr_rw, so here this register is simply set to 1.

  // The extclk cannot be manipulated in low power mode.
  constraint io_ip_clk_en_on_c {io_ip_clk_en == 1'b1;}
  constraint main_ip_clk_en_on_c {main_ip_clk_en == 1'b1;}
  constraint usb_ip_clk_en_on_c {usb_ip_clk_en == 1'b1;}

  // This randomizes the time when the extclk_ctrl CSR write and the lc_clk_byp_req
  // input is asserted for good measure. Of course, there is a good chance only a single
  // one of these trigger a request, so they are also independently tested.
  rand int cycles_before_extclk_ctrl_sel;
  rand int cycles_before_lc_clk_byp_req;
  rand int cycles_before_lc_clk_byp_ack;
  rand int cycles_before_all_clk_byp_ack;
  rand int cycles_before_io_clk_byp_ack;
  rand int cycles_before_next_trans;

  constraint cycles_to_stim_c {
    cycles_before_extclk_ctrl_sel inside {[4 : 20]};
    cycles_before_lc_clk_byp_req inside {[4 : 20]};
    cycles_before_lc_clk_byp_ack inside {[12 : 20]};
    cycles_before_all_clk_byp_ack inside {[3 : 11]};
    cycles_before_io_clk_byp_ack inside {[3 : 11]};
    cycles_before_next_trans inside {[15 : 25]};
  }

  lc_tx_t lc_clk_byp_req;
  lc_tx_t lc_debug_en;

  function void post_randomize();
    lc_clk_byp_req = get_rand_lc_tx_val(8, 2, 2);
    lc_debug_en = get_rand_lc_tx_val(8, 2, 2);
    `uvm_info(`gfn, $sformatf(
              "randomize gives lc_clk_byp_req=0x%x, lc_debug_en=0x%x", lc_clk_byp_req, lc_debug_en),
              UVM_MEDIUM)
    super.post_randomize();
  endfunction

  // Notice only all_clk_byp_req and io_clk_byp_req Mubi4True and Mubi4False cause transitions.

  local task all_clk_byp_handshake();
    forever
      @cfg.clkmgr_vif.all_clk_byp_req begin : all_clk_byp_ack
        if (cfg.clkmgr_vif.all_clk_byp_req == prim_mubi_pkg::MuBi4True) begin
          `uvm_info(`gfn, "Got all_clk_byp_req on", UVM_MEDIUM)
          cfg.clk_rst_vif.wait_clks(cycles_before_all_clk_byp_ack);
          cfg.clkmgr_vif.update_all_clk_byp_ack(prim_mubi_pkg::MuBi4True);
        end else if (cfg.clkmgr_vif.all_clk_byp_req == prim_mubi_pkg::MuBi4False) begin
          `uvm_info(`gfn, "Got all_clk_byp_req off", UVM_MEDIUM)
          cfg.clk_rst_vif.wait_clks(cycles_before_all_clk_byp_ack);
          cfg.clkmgr_vif.update_all_clk_byp_ack(prim_mubi_pkg::MuBi4False);
        end
      end
  endtask

  local task io_clk_byp_handshake();
    forever
      @cfg.clkmgr_vif.io_clk_byp_req begin : io_clk_byp_ack
        if (cfg.clkmgr_vif.io_clk_byp_req == prim_mubi_pkg::MuBi4True) begin
          `uvm_info(`gfn, "Got io_clk_byp_req on", UVM_MEDIUM)
          cfg.clk_rst_vif.wait_clks(cycles_before_io_clk_byp_ack);
          cfg.clkmgr_vif.update_io_clk_byp_ack(prim_mubi_pkg::MuBi4True);
        end else begin
          `uvm_info(`gfn, "Got io_clk_byp_req off", UVM_MEDIUM)
          cfg.clk_rst_vif.wait_clks(cycles_before_io_clk_byp_ack);
          cfg.clkmgr_vif.update_io_clk_byp_ack(prim_mubi_pkg::MuBi4False);
        end
      end
  endtask

  local task lc_clk_byp_handshake();
    forever
      @cfg.clkmgr_vif.lc_clk_byp_ack begin : lc_clk_byp_ack
        if (cfg.clkmgr_vif.lc_clk_byp_ack == lc_ctrl_pkg::On) begin
          `uvm_info(`gfn, "Got lc_clk_byp_ack on", UVM_MEDIUM)
        end
      end
  endtask

  local task run_test();
    for (int i = 0; i < num_trans; ++i) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      // Init needs to be synchronous.
      @cfg.clk_rst_vif.cb begin
        cfg.clkmgr_vif.init(.idle(idle), .scanmode(scanmode), .lc_debug_en(lc_debug_en));
        control_ip_clocks();
      end
      fork
        begin
          cfg.clk_rst_vif.wait_clks(cycles_before_extclk_ctrl_sel);
          csr_wr(.ptr(ral.extclk_ctrl), .value({extclk_ctrl_low_speed_sel, extclk_ctrl_sel}));
        end
        begin
          cfg.clk_rst_vif.wait_clks(cycles_before_lc_clk_byp_req);
          cfg.clkmgr_vif.update_lc_clk_byp_req(lc_clk_byp_req);
        end
      join
      `uvm_info(`gfn, $sformatf(
                {
                  "extclk_ctrl_sel=0x%0x, extclk_ctrl_low_speed_sel=0x%0x, lc_clk_byp_req=0x%0x, ",
                  "lc_debug_en=0x%0x, scanmode=0x%0x"
                },
                extclk_ctrl_sel,
                extclk_ctrl_low_speed_sel,
                lc_clk_byp_req,
                lc_debug_en,
                scanmode
                ), UVM_MEDIUM)
      csr_rd_check(.ptr(ral.extclk_ctrl),
                   .compare_value({extclk_ctrl_low_speed_sel, extclk_ctrl_sel}));
      if (lc_clk_byp_req == lc_ctrl_pkg::On) begin
        wait(cfg.clkmgr_vif.lc_clk_byp_req == lc_ctrl_pkg::On);
        cfg.clk_rst_vif.wait_clks(cycles_before_lc_clk_byp_ack);
        cfg.clkmgr_vif.update_lc_clk_byp_req(lc_ctrl_pkg::Off);
      end
      // Disable extclk software control.
      csr_wr(.ptr(ral.extclk_ctrl), .value({Off, Off}));
      cfg.clk_rst_vif.wait_clks(cycles_before_next_trans);
    end
  endtask

  task body();
    set_scanmode_on_low_weight();
    csr_wr(.ptr(ral.extclk_ctrl_regwen), .value(1));

    fork
      begin : isolation_fork
        fork
          all_clk_byp_handshake();
          io_clk_byp_handshake();
          lc_clk_byp_handshake();
          run_test();
        join_any
        disable fork;
      end
    join
  endtask

endclass
