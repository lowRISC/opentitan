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
  rand int cycles_before_div_step_down_req;
  rand int cycles_before_io_clk_byp_ack;
  rand int cycles_before_next_trans;

  rand int flips_before_io_clk_byp_ack;
  rand int flips_before_div_step_down_req;
  rand int flips_before_all_clk_byp_ack;
  rand int cycles_between_flips;

  constraint cycles_to_stim_c {
    cycles_before_extclk_ctrl_sel inside {[4 : 20]};
    cycles_before_lc_clk_byp_req inside {[4 : 20]};
    cycles_before_lc_clk_byp_ack inside {[16 : 30]};
    cycles_before_all_clk_byp_ack inside {[3 : 11]};
    cycles_before_div_step_down_req inside {[3 : 11]};
    cycles_before_io_clk_byp_ack inside {[3 : 11]};
    cycles_before_next_trans inside {[15 : 35]};
    flips_before_io_clk_byp_ack inside {[0 : 3]};
    flips_before_div_step_down_req inside {[0 : 3]};
    flips_before_all_clk_byp_ack inside {[0 : 3]};
    cycles_between_flips inside {[3 : 5]};
  }

  lc_tx_t lc_clk_byp_req;
  lc_tx_t lc_debug_en;
  mubi4_t io_clk_byp_ack_non_true;
  mubi4_t all_clk_byp_ack_non_true;
  mubi4_t div_step_down_req_non_true;

  mubi4_t exp_all_clk_byp_ack;

  function void post_randomize();
    if (mubi_mode == ClkmgrMubiLcHand) begin
      // increase weight of illegal value only in ClkmgrMubiLcHand
      lc_clk_byp_req = get_rand_lc_tx_val(.t_weight(1), .f_weight(1), .other_weight(14));
    end else begin
      lc_clk_byp_req = get_rand_lc_tx_val(.t_weight(8), .f_weight(2), .other_weight(2));
    end
    if (mubi_mode == ClkmgrMubiLcCtrl) begin
      // increase weight of illgal value only in ClkmgrMubiLcHand
      lc_debug_en = get_rand_lc_tx_val(.t_weight(1), .f_weight(1), .other_weight(14));
    end else begin
      lc_debug_en = get_rand_lc_tx_val(.t_weight(8), .f_weight(2), .other_weight(2));
    end

    io_clk_byp_ack_non_true = get_rand_mubi4_val(.t_weight(0), .f_weight(2), .other_weight(8));
    all_clk_byp_ack_non_true = get_rand_mubi4_val(.t_weight(0), .f_weight(2), .other_weight(8));
    div_step_down_req_non_true = get_rand_mubi4_val(.t_weight(0), .f_weight(2), .other_weight(8));

    `uvm_info(`gfn, $sformatf(
              "randomize gives lc_clk_byp_req=0x%x, lc_debug_en=0x%x", lc_clk_byp_req, lc_debug_en),
              UVM_MEDIUM)
    super.post_randomize();

    extclk_ctrl_sel = get_rand_mubi4_val(.t_weight(8), .f_weight(1), .other_weight(1));
    `uvm_info(`gfn, $sformatf("overwrite extclk_ctrl_sel=0x%x", extclk_ctrl_sel), UVM_MEDIUM)

  endfunction

  // Notice only all_clk_byp_req and io_clk_byp_req Mubi4True and Mubi4False cause transitions.
  local task delayed_update_all_clk_byp_ack(mubi4_t value, int cycles);
    uvm_reg_data_t rd_data;

    if (mubi_mode == ClkmgrMubiHand && value == MuBi4True) begin
      repeat (flips_before_all_clk_byp_ack) begin
        exp_all_clk_byp_ack = get_rand_mubi4_val(.t_weight(0), .f_weight(1), .other_weight(1));
        cfg.clk_rst_vif.wait_clks(cycles_between_flips);
        cfg.clkmgr_vif.update_all_clk_byp_ack(exp_all_clk_byp_ack);
        cfg.clk_rst_vif.wait_clks(4);
        csr_rd(.ptr(ral.extclk_status), .value(rd_data));
        // csr_rd_check didn't work well for status register read check
        `DV_CHECK_EQ(exp_all_clk_byp_ack, rd_data, "extclk_status mismatch")
      end
    end
    cfg.clk_rst_vif.wait_clks(cycles_between_flips);
    cfg.clkmgr_vif.update_all_clk_byp_ack(value);
  endtask

  local task delayed_update_div_step_down_req(mubi4_t value, int cycles);
    if (mubi_mode == ClkmgrMubiDiv && value == MuBi4True) begin
      repeat (flips_before_div_step_down_req) begin
        cfg.clk_rst_vif.wait_clks(cycles_between_flips);
        cfg.clkmgr_vif.update_div_step_down_req(get_rand_mubi4_val(
                                                .t_weight(0), .f_weight(1), .other_weight(1)));
      end
    end
    cfg.clk_rst_vif.wait_clks(cycles_between_flips);
    `uvm_info(`gfn, $sformatf("Settling div_step_down_req to 0x%x", value), UVM_MEDIUM)
    cfg.clkmgr_vif.update_div_step_down_req(value);
  endtask

  local task delayed_update_io_clk_byp_ack(mubi4_t value, int cycles);
    if (mubi_mode == ClkmgrMubiHand && value == MuBi4True) begin
      repeat (flips_before_io_clk_byp_ack) begin
        cfg.clk_rst_vif.wait_clks(cycles_between_flips);
        cfg.clkmgr_vif.update_io_clk_byp_ack(get_rand_mubi4_val(
                                             .t_weight(0), .f_weight(1), .other_weight(1)));
      end
    end
    cfg.clk_rst_vif.wait_clks(cycles_between_flips);
    `uvm_info(`gfn, $sformatf("Settling io_clk_byp_ack to 0x%x", value), UVM_MEDIUM)
    cfg.clkmgr_vif.update_io_clk_byp_ack(value);
  endtask

  local task all_clk_byp_handshake();
    forever
      @cfg.clkmgr_vif.all_clk_byp_req begin : all_clk_byp_ack
        if (cfg.clkmgr_vif.all_clk_byp_req == prim_mubi_pkg::MuBi4True) begin
          `uvm_info(`gfn, "Got all_clk_byp_req on", UVM_MEDIUM)
          fork
            delayed_update_all_clk_byp_ack(MuBi4True, cycles_before_all_clk_byp_ack);
            delayed_update_div_step_down_req(MuBi4True, cycles_before_div_step_down_req);
          join
        end else begin
          `uvm_info(`gfn, "Got all_clk_byp_req off", UVM_MEDIUM)
          // Set inputs to mubi4 non-True.
          fork
            delayed_update_all_clk_byp_ack(all_clk_byp_ack_non_true, cycles_before_all_clk_byp_ack);
            delayed_update_div_step_down_req(div_step_down_req_non_true,
                                             cycles_before_div_step_down_req);
          join
        end
      end
  endtask

  local task io_clk_byp_handshake();
    forever
      @cfg.clkmgr_vif.io_clk_byp_req begin : io_clk_byp_ack
        if (cfg.clkmgr_vif.io_clk_byp_req == MuBi4True) begin
          `uvm_info(`gfn, "Got io_clk_byp_req True", UVM_MEDIUM)
          fork
            delayed_update_io_clk_byp_ack(MuBi4True, cycles_before_io_clk_byp_ack);
            delayed_update_div_step_down_req(MuBi4True, cycles_before_div_step_down_req);
          join
        end else begin
          `uvm_info(`gfn, "Got io_clk_byp_req non True", UVM_MEDIUM)
          // Set inputs to mubi4 non-True.
          fork
            delayed_update_io_clk_byp_ack(io_clk_byp_ack_non_true, cycles_before_io_clk_byp_ack);
            delayed_update_div_step_down_req(div_step_down_req_non_true,
                                             cycles_before_div_step_down_req);
          join
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
          csr_wr(.ptr(ral.extclk_ctrl), .value({extclk_ctrl_high_speed_sel, extclk_ctrl_sel}));
        end
        begin
          cfg.clk_rst_vif.wait_clks(cycles_before_lc_clk_byp_req);
          cfg.clkmgr_vif.update_lc_clk_byp_req(lc_clk_byp_req);
        end
      join
      `uvm_info(`gfn, $sformatf(
                {
                  "extclk_ctrl_sel=0x%0x, extclk_ctrl_high_speed_sel=0x%0x, lc_clk_byp_req=0x%0x, ",
                  "lc_debug_en=0x%0x, scanmode=0x%0x"
                },
                extclk_ctrl_sel,
                extclk_ctrl_high_speed_sel,
                lc_clk_byp_req,
                lc_debug_en,
                scanmode
                ), UVM_MEDIUM)
      csr_rd_check(.ptr(ral.extclk_ctrl),
                   .compare_value({extclk_ctrl_high_speed_sel, extclk_ctrl_sel}));
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
