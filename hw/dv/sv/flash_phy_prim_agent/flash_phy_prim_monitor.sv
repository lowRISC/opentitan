// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_phy_prim_monitor extends dv_base_monitor #(
    .ITEM_T (flash_phy_prim_item),
    .CFG_T  (flash_phy_prim_agent_cfg),
    .COV_T  (flash_phy_prim_agent_cov)
  );
  `uvm_component_utils(flash_phy_prim_monitor)

  // the base class provides the following handles for use:
  // flash_phy_prim_agent_cfg: cfg
  // flash_phy_prim_agent_cov: cov

  uvm_analysis_port #(flash_phy_prim_item) eg_rtl_port[NumBanks];
  uvm_analysis_port #(flash_phy_prim_item) rd_cmd_port[NumBanks];
  uvm_analysis_port #(flash_phy_prim_item) eg_rtl_lm_port[NumBanks];
  flash_phy_prim_item w_item[NumBanks];
  flash_phy_prim_item r_item[NumBanks];
  flash_phy_prim_item lm_item[NumBanks];
  logic [PhyDataW-1:0] write_buffer[NumBanks][$];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    foreach (eg_rtl_port[i]) begin
      eg_rtl_port[i] = new($sformatf("eg_rtl_port[%0d]", i), this);
      rd_cmd_port[i] = new($sformatf("rd_cmd_port[%0d]", i), this);
      eg_rtl_lm_port[i] = new($sformatf("eg_rtl_lm_port[%0d]", i), this);
    end
  endfunction

  task reset_task;
    forever begin
      @(negedge cfg.vif.rst_n);
      foreach (write_buffer[i]) write_buffer[i] = '{};
    end
  endtask // reset_task

  task run_phase(uvm_phase phase);
    if (cfg.scb_otf_en) begin
      `DV_SPINWAIT(wait(cfg.mon_start);,
                   "timeout waiting for mon_start", 500_000)
      fork
        super.run_phase(phase);
        monitor_core();
        reset_task();
      join_none
    end
  endtask

  // Capture read request from flash_core
  task monitor_core();
    `DV_SPINWAIT(wait(cfg.vif.rst_n == 1);,
                 "timeout waiting for reset deassert", 100_000)
    if (cfg.scb_otf_en) begin
      for (int i = 0; i < NumBanks; ++i) begin
        automatic int j = i;
        fork begin
          // Assuming tb.dut.u_eflash.gen_flash_cores[bank].u_core.u_rd.req_i
          // is one cycle per transaction.
          forever begin
            @cfg.vif.cb;
            #0.1ns;
            if (cfg.vif.rreq[j] & cfg.vif.rdy[j]) begin
              r_item[j] = flash_phy_prim_item::type_id::create($sformatf("r_item[%0d]", j));
              r_item[j].req = cfg.vif.req[j];
              eg_rtl_port[j].write(r_item[j]);
            end
          end
        end join_none
      end
    end
  endtask

  // collect transactions forever - already forked in dv_base_monitor::run_phase
  virtual protected task collect_trans(uvm_phase phase);
    `DV_SPINWAIT(wait(cfg.vif.rst_n == 1);,
                 "timeout waiting for reset deassert", 100_000)
    `uvm_info(`gfn, $sformatf("flash_phy_prim_monitor %s", (cfg.scb_otf_en)? "enabled" :
                              "disabled"), UVM_MEDIUM)

    if (cfg.scb_otf_en) begin
      fork
        for (int i = 0; i < NumBanks; ++i) begin
          automatic int j = i;
          fork begin
            forever begin
              @cfg.vif.cb;
              #0.1ns;
              if (cfg.vif.rsp[j].ack) begin
                if (cfg.vif.req[j].rd_req & cfg.vif.req[j].prog_req) begin
                  `uvm_error(`gfn, $sformatf("Both prog and rd req are set"))
                end else if (~cfg.vif.req[j].rd_req & cfg.vif.req[j].prog_req) begin
                  // collect transaction for last time check
                  collect_lm_item(j);
                  collect_wr_data(j);
                end else if (cfg.vif.req[j].rd_req) begin
                  collect_rd_cmd(j);
                end else if (cfg.vif.req[j].pg_erase_req | cfg.vif.req[j].bk_erase_req |
                             cfg.vif.req[j].erase_suspend_req) begin
                  // collect erase error transactions
                  collect_lm_item(j);
                end
              end
            end
          end join_none
        end
      join_none
    end
  endtask // collect_trans

  task collect_rd_cmd(int bank);
    flash_phy_prim_item rcmd;
    rcmd = flash_phy_prim_item::type_id::create("rcmd");
    rcmd.req = cfg.vif.req[bank];

    rd_cmd_port[bank].write(rcmd);
  endtask // collect_rd_cmd

  task collect_wr_data(int bank);
    if (write_buffer[bank].size() == 0) begin
      w_item[bank] = flash_phy_prim_item::type_id::create($sformatf("w_item[%0d]", bank));
      w_item[bank].req = cfg.vif.req[bank];
      w_item[bank].rsp = cfg.vif.rsp[bank];
      `uvm_info(`gfn, $sformatf("MON%0d s_addr:%x",bank, w_item[bank].req.addr), UVM_HIGH)
    end

    write_buffer[bank].push_back(cfg.vif.req[bank].prog_full_data);

    if (cfg.vif.req[bank].prog_last) begin
      w_item[bank].fq = write_buffer[bank];
      eg_rtl_port[bank].write(w_item[bank]);
      `uvm_info(`gfn, $sformatf("MON%0d: wbuf:%0d    fq:%0d", bank,
                                write_buffer[bank].size(), w_item[bank].fq.size()), UVM_HIGH)
      write_buffer[bank] = {};
    end
  endtask // collect_item
  function void collect_lm_item(int bank);
    flash_phy_prim_item item;
    `uvm_create_obj(flash_phy_prim_item, item)
    item.req = cfg.vif.req[bank];
    item.rsp = cfg.vif.rsp[bank];
    eg_rtl_lm_port[bank].write(item);
    `uvm_info("lm_debug", $sformatf("I sent bank%0d", bank),UVM_MEDIUM)
  endfunction // collect_lm_item

endclass
