class rv_dm_sba_debug_disabled_vseq extends rv_dm_sba_tl_access_vseq;
  `uvm_object_utils(rv_dm_sba_debug_disabled_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
   }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }

  task body();
   repeat ($urandom_range(1, 10)) begin
      csr_wr(.ptr(jtag_dmi_ral.dmcontrol.dmactive), .value(1));
      req = sba_access_item::type_id::create("req");
      randomize_req(req);
      cfg.debugger.sba_access(req);
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      cfg.rv_dm_vif.lc_hw_debug_en<=lc_ctrl_pkg::Off;
      csr_wr(.ptr(jtag_dmi_ral.dmcontrol.dmactive), .value(1));
      req = sba_access_item::type_id::create("req");
      randomize_req(req);
      cfg.debugger.sba_access(req);
      `DV_CHECK_EQ(req.is_err, SbaErrNone)
   end
  endtask : body
endclass  : rv_dm_sba_debug_disabled_vseq
