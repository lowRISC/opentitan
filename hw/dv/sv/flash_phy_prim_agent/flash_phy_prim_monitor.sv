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

  uvm_analysis_port #(flash_phy_prim_item) eg_rtl_port[flash_ctrl_pkg::NumBanks];
  flash_phy_prim_item w_item[flash_ctrl_pkg::NumBanks];
  logic [flash_phy_pkg::FullDataWidth-1:0] write_buffer[flash_ctrl_pkg::NumBanks][$];
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    foreach(eg_rtl_port[i]) begin
      eg_rtl_port[i] = new($sformatf("eg_rtl_port[%0d]", i), this);
    end

  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
  endtask

  // collect transactions forever - already forked in dv_base_monitor::run_phase
  virtual protected task collect_trans(uvm_phase phase);
    wait(cfg.vif.rst_n == 1);

    `uvm_info(`gfn, $sformatf("flash_phy_prim_monitor %s", (cfg.scb_otf_en)? "enabled" :
                              "disabled"), UVM_MEDIUM)

    if (cfg.scb_otf_en) begin
      fork
        for (int i = 0; i < flash_ctrl_pkg::NumBanks; ++i) begin
          automatic int j = i;
          fork begin
            forever begin
              @cfg.vif.cb;
              if (cfg.vif.rsp[j].ack) begin
                if (~cfg.vif.req[j].rd_req & ~cfg.vif.req[j].prog_req) begin
                  // do nothing
                end else if (cfg.vif.req[j].rd_req & ~cfg.vif.req[j].prog_req) begin
                  // TBD collect read
                end else if (~cfg.vif.req[j].rd_req & cfg.vif.req[j].prog_req) begin
                  collect_wr_data(j);
                end else begin
                  `uvm_error(`gfn, $sformatf("Both prog and rd req is set"))
                end
              end
            end
          end join_none
        end
      join_none
    end
  endtask // collect_trans

  task collect_wr_data(int bank);
    if (write_buffer[bank].size() == 0) begin
      w_item[bank] = flash_phy_prim_item::type_id::create($sformatf("w_item[%0d]", bank));
      w_item[bank].req = cfg.vif.req[bank];
      w_item[bank].rsp = cfg.vif.rsp[bank];
    end

    write_buffer[bank].push_back(cfg.vif.req[bank].prog_full_data);

    if (cfg.vif.req[bank].prog_last) begin
      w_item[bank].fq = write_buffer[bank];
      eg_rtl_port[bank].write(w_item[bank]);
      write_buffer[bank] = {};
    end
  endtask // collect_item

endclass
