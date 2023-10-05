//rv_dm_jtag_dtm_idle_hint_vseq
// in this sequence i got timeout error.
class rv_dm_jtag_dtm_idle_hint_vseq  extends rv_dm_base_vseq;
`uvm_object_utils(rv_dm_jtag_dtm_idle_hint_vseq)
 `uvm_object_new

   constraint lc_hw_debug_en_c {
	lc_hw_debug_en == lc_ctrl_pkg::On;
   }

   constraint scanmode_c {
        scanmode == prim_mubi_pkg::MuBi4False;
   }

   task body();
     uvm_reg_data_t wdata;
     uvm_reg_data_t rdata;
     wdata= $urandom_range(0,31);
     csr_rd(.ptr(jtag_dtm_ral.dtmcs), .value(rdata));
     `DV_CHECK_EQ(1,get_field_val(jtag_dtm_ral.dtmcs.idle,rdata))
     csr_wr(.ptr(jtag_dtm_ral.dmi), .value('h1037652002));
     csr_wr(.ptr(jtag_dtm_ral.dmi), .value('h803652002));
     csr_wr(.ptr(jtag_dtm_ral.dmi), .value('h5c3002002));
     csr_rd(.ptr(jtag_dtm_ral.dtmcs), .value(rdata));
     `DV_CHECK_EQ(0,get_field_val(jtag_dtm_ral.dtmcs.dmistat,rdata))
   endtask

endclass : rv_dm_jtag_dtm_idle_hint_vseq
///////////////////////////////////////////////////////////////////

//rv_dm_jtag_dtm_hard_reset_vseq
//test is not passing because even after write to dmihardreset, value is written on target dmi register.
class rv_dm_jtag_dtm_hard_reset_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_jtag_dtm_hard_reset_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
   }
    task body();
    uvm_reg_data_t wdata;
    uvm_reg_data_t rdata;
    wdata=$urandom_range(0,1);
      csr_wr(.ptr(jtag_dtm_ral.dmi), .value('h8045321102), .blocking(0), .predict(1));
      csr_wr(.ptr(jtag_dtm_ral.dtmcs.dmihardreset), .value(1), .blocking(1), .predict(1));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      csr_rd(.ptr(jtag_dmi_ral.progbuf[0]), .value(rdata));
     `DV_CHECK_EQ(rdata, jtag_dmi_ral.progbuf[0].get_reset());
  endtask

endclass : rv_dm_jtag_dtm_hard_reset_vseq

///////////////////////////////////////////////////////////////////
//rv_dm_jtag_dtm_hard_reset_vseq(other way)
//when i write sequence this way then it passed.it cancle ongoing transactions but data is again written on target dmi register. 

class rv_dm_jtag_dtm_hard_reset_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_jtag_dtm_hard_reset_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
   }
    task body();
    uvm_reg_data_t wdata;
    uvm_reg_data_t rdata;
    wdata=$urandom_range(0,1);
      csr_wr(.ptr(jtag_dtm_ral.dmi), .value('h8045321102), .blocking(0), .predict(1));
      csr_wr(.ptr(jtag_dtm_ral.dtmcs.dmihardreset), .value(1), .blocking(1), .predict(1));
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 1000));
      csr_rd(.ptr(jtag_dtm_ral.dmi), .value(rdata));
     `DV_CHECK_EQ(rdata, jtag_dtm_ral.dmi.data.get_reset());
      csr_rd(.ptr(jtag_dmi_ral.progbuf[0]), .value(rdata));
  endtask

endclass : rv_dm_jtag_dtm_hard_reset_vseq

