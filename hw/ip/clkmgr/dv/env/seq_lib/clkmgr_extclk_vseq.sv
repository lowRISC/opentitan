// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The extclk vseq causes the external clock selection to be triggered. More details
// in the clkmgr_testplan.hjson file.
class clkmgr_extclk_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_extclk_vseq)

  `uvm_object_new

  // If the extclk_sel_regwen is clear, it is not possible to select external clocks.
  // This is tested in regular csr_rw, so here this register is simply set to 1.

  // lc_dft_en is set according to sel_lc_dft_en, which is randomized with weights.
  lc_tx_t            lc_dft_en;
  rand lc_tx_t       lc_dft_en_other;
  rand lc_tx_t_sel_e sel_lc_dft_en;

  constraint lc_dft_en_c {
    sel_lc_dft_en dist {
      LcTxTSelOn    := 8,
      LcTxTSelOff   := 2,
      LcTxTSelOther := 2
    };
    !(lc_dft_en_other inside {On, Off});
  }

  // lc_clk_byp_req is set according to sel_lc_clk_byp_req, which is randomized with weights.
  lc_tx_t            lc_clk_byp_req;
  rand lc_tx_t       lc_clk_byp_req_other;
  rand lc_tx_t_sel_e sel_lc_clk_byp_req;

  constraint lc_clk_byp_req_c {
    sel_lc_clk_byp_req dist {
      LcTxTSelOn    := 8,
      LcTxTSelOff   := 2,
      LcTxTSelOther := 2
    };
    !(lc_clk_byp_req_other inside {On, Off});
  }

  // This randomizes the time when the extclk_sel CSR write and the lc_clk_byp_req
  // input is asserted for good measure. Of course, there is a good chance only a single
  // one of these trigger a request, so they are also independently tested.
  rand int cycles_before_extclk_sel;
  rand int cycles_before_lc_clk_byp_req;
  rand int cycles_before_lc_clk_byp_ack;
  rand int cycles_before_ast_clk_byp_ack;
  rand int cycles_before_next_trans;

  constraint cycles_to_stim_c {
    cycles_before_extclk_sel inside {[4 : 20]};
    cycles_before_lc_clk_byp_req inside {[4 : 20]};
    cycles_before_lc_clk_byp_ack inside {[4 : 20]};
    cycles_before_ast_clk_byp_ack inside {[3 : 11]};
    cycles_before_next_trans inside {[15 : 25]};
  }

  function void post_randomize();
    super.post_randomize();
    lc_dft_en = get_lc_tx_t_from_sel(sel_lc_dft_en, lc_dft_en_other);
    lc_clk_byp_req = get_lc_tx_t_from_sel(sel_lc_clk_byp_req, lc_clk_byp_req_other);
  endfunction

  task body();
    update_csrs_with_reset_values();
    set_scanmode_on_low_weight();
    csr_wr(.ptr(ral.extclk_sel_regwen), .value(1));
    fork
      forever
        @cfg.clkmgr_vif.ast_clk_byp_req begin : ast_clk_byp_ack
          if (cfg.clkmgr_vif.ast_clk_byp_req == lc_ctrl_pkg::On) begin
            `uvm_info(`gfn, "Got ast_clk_byp_req on", UVM_MEDIUM)
            cfg.clk_rst_vif.wait_clks(cycles_before_ast_clk_byp_ack);
            cfg.clkmgr_vif.update_ast_clk_byp_ack(lc_ctrl_pkg::On);
          end else begin
            `uvm_info(`gfn, "Got ast_clk_byp_req off", UVM_MEDIUM)
            cfg.clk_rst_vif.wait_clks(cycles_before_ast_clk_byp_ack);
            cfg.clkmgr_vif.update_ast_clk_byp_ack(lc_ctrl_pkg::Off);
          end
        end
      forever
        @cfg.clkmgr_vif.lc_clk_byp_ack begin : lc_clk_byp_ack
          if (cfg.clkmgr_vif.lc_clk_byp_ack == lc_ctrl_pkg::On) begin
            `uvm_info(`gfn, "Got lc_clk_byp_ack on", UVM_MEDIUM)
          end else begin
            `uvm_info(`gfn, "Got lc_clk_byp_req off", UVM_MEDIUM)
            cfg.clk_rst_vif.wait_clks(cycles_before_lc_clk_byp_ack);
            cfg.clkmgr_vif.update_lc_clk_byp_req(lc_ctrl_pkg::Off);
          end
        end
    join_none
    for (int i = 0; i < num_trans; ++i) begin
      logic [TL_DW-1:0] value;
      `DV_CHECK_RANDOMIZE_FATAL(this)
      // Init needs to be synchronous.
      @cfg.clk_rst_vif.cb begin
        cfg.clkmgr_vif.init(.idle(idle), .ip_clk_en(ip_clk_en), .scanmode(scanmode),
                            .lc_dft_en(lc_dft_en));
      end
      fork
        begin
          cfg.clk_rst_vif.wait_clks(cycles_before_extclk_sel);
          csr_wr(.ptr(ral.extclk_sel), .value(extclk_sel));
        end
        begin
          cfg.clk_rst_vif.wait_clks(cycles_before_lc_clk_byp_req);
          cfg.clkmgr_vif.update_lc_clk_byp_req(lc_clk_byp_req);
        end
      join
      `uvm_info(`gfn, $sformatf(
                "extclk_sel=0x%0x, lc_clk_byp_req=0x%0x, lc_dft_en=0x%0x, scanmode=0x%0x",
                extclk_sel,
                lc_clk_byp_req,
                lc_dft_en,
                scanmode
                ), UVM_MEDIUM)
      csr_rd_check(.ptr(ral.extclk_sel), .compare_value(extclk_sel));
      cfg.io_clk_rst_vif.wait_clks(cycles_before_next_trans);
    end
    disable fork;
  endtask

endclass
