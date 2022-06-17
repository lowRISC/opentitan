// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_otf_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(flash_ctrl_otf_scoreboard)
  `uvm_component_new

  // OTF data path fifos
  // Assuming egress (host -> flash) ordering is  maintained per bank.
  uvm_tlm_analysis_fifo #(flash_otf_item) eg_exp_fifo[flash_ctrl_pkg::NumBanks];
  uvm_tlm_analysis_fifo #(flash_phy_prim_item) eg_rtl_fifo[flash_ctrl_pkg::NumBanks];
  flash_ctrl_env_cfg cfg;

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    foreach(eg_exp_fifo[i]) begin
      eg_exp_fifo[i] = new($sformatf("eg_exp_fifo[%0d]", i), this);
      eg_rtl_fifo[i] = new($sformatf("eg_rtl_fifo[%0d]", i), this);
    end
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    uvm_config_db#(flash_ctrl_env_cfg)::get(this, "", "cfg", cfg);
  endfunction // connect_phase

  task run_phase(uvm_phase phase);
    flash_otf_item  exp_item[flash_ctrl_pkg::NumBanks];
    fork
      begin
        foreach (eg_exp_fifo[i]) begin
          automatic int j = i;
          fork begin
            forever begin
              eg_exp_fifo[j].get(exp_item[j]);
              process_eg(exp_item[j], j);
            end
          end join_none
        end
      end
    join_none
  endtask // run_phase

  task process_eg(flash_otf_item exp, int bank);
    flash_phy_prim_item  item;
    flash_otf_item       obs;
    int col_sz = exp.fq.size / 8;

    eg_rtl_fifo[bank].get(item);
    `uvm_create_obj(flash_otf_item, obs)
    obs.get_wd_from_phy(item);
    obs.fq = item.fq;

    repeat(col_sz - 1) begin
      eg_rtl_fifo[bank].get(item);
      obs.fq = {obs.fq, item.fq};
    end

    compare_wdata(obs, exp, bank);
  endtask // process_eg

  // Compare 64 bit for now
  task compare_wdata(flash_otf_item obs,
                     flash_otf_item exp, int bank);
    string str = $sformatf("wdata_comp_bank%0d", bank);
    bit    err = 0;
    `dv_info($sformatf(" Wdata size: %d x 8B  rcvd_cnt:%0d",
                       obs.fq.size(), cfg.otf_ctrl_wr_rcvd++), UVM_MEDIUM, str)
    foreach(obs.fq[i]) begin
      if (obs.fq[i][63:0] != exp.fq[i][63:0]) begin
        err = 1;
        `dv_error($sformatf("%4d: obs:exp    %8x_%8x:%8x_%8x  mismatch!!", i,
                  obs.fq[i][63:32], obs.fq[i][31:0], exp.fq[i][63:32], exp.fq[i][31:0]),
                  str)
      end
    end
    if (err == 0) begin
      `dv_info("data match!!", UVM_MEDIUM, str)
    end
  endtask // compare_wdata

endclass
