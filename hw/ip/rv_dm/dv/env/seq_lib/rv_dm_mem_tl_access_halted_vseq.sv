// HALTED test vseq
class rv_dm_mem_tl_access_halted_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_mem_tl_access_halted_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }
  
  task body();   
    uvm_reg_data_t rw_data;
    repeat ($urandom_range(1, 10)) begin
      rw_data = $urandom_range(0, 1);
      // Verify that writing to HALTED results in anyhalted and allhalted to be set.
      csr_wr(.ptr(jtag_dmi_ral.dmcontrol.haltreq), .value(1));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      csr_wr(.ptr(tl_mem_ral.halted), .value(rw_data));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(rw_data));
      `DV_CHECK_EQ(1, get_field_val(jtag_dmi_ral.dmstatus.anyhalted, rw_data))      
      `DV_CHECK_EQ(1, get_field_val(jtag_dmi_ral.dmstatus.allhalted, rw_data))
      cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
    end  
  endtask : body
  
endclass : rv_dm_mem_tl_access_halted_vseq
