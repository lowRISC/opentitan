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
  int dbg1 = 0;
  int dbg2 = 0;

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
    flash_otf_item       exp_item[flash_ctrl_pkg::NumBanks];

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

  task process_eg(flash_otf_item item, int bank);
    `JDBG(("EXPGET: op:%s fq:%0d dbg:%0d rtlff:%0d", item.cmd.op.name(), item.fq.size(), dbg1++, eg_rtl_fifo[bank].used()))
    case(item.cmd.op)
      FlashOpProgram:begin
        process_write(item, bank);
      end
      FlashOpRead:begin
        process_read(item, bank);
      end
      default:begin
      end
    endcase
  endtask

  task process_read(flash_otf_item exp, int bank);
    flash_phy_prim_item  item;
    flash_otf_item       obs;
    int col_sz = exp.fq.size;
    `JDBG(("process_read:bank:%0d colsz:%0d ffsz:%0d", bank, col_sz, eg_rtl_fifo[bank].used()))
    exp.print("exp_read");

    eg_rtl_fifo[bank].get(item);
    `uvm_create_obj(flash_otf_item, obs)
    obs.get_from_phy(item, "r");

    repeat(col_sz - 1) begin
      eg_rtl_fifo[bank].get(item);
      obs.fq = {obs.fq, item.fq};
    end

    obs.print("rtl_read: enc_data");
    obs.descramble(exp.addr_key, exp.data_key);
//    obs.print("rtl_read: after");
    `dv_info($sformatf("RDATA size: %d x 8B bank:%0d sent_cnt:%0d",
                       obs.raw_fq.size(), bank, cfg.otf_ctrl_rd_sent++), UVM_MEDIUM, "process_read")
    compare_data(obs.raw_fq, exp.fq, bank, "rdata");
  endtask

  task process_write(flash_otf_item exp, int bank);
    flash_phy_prim_item  item;
    flash_otf_item       obs;
    int col_sz = exp.fq.size / 8;

    `JDBG(("process_write:col&comp:bank:%0d colsz:%0d ffsz:%0d", bank, col_sz, eg_rtl_fifo[bank].used()))
    eg_rtl_fifo[bank].get(item);
    `uvm_create_obj(flash_otf_item, obs)
    obs.get_from_phy(item, "w");
    obs.fq = item.fq;

    repeat(col_sz - 1) begin
      eg_rtl_fifo[bank].get(item);
      obs.fq = {obs.fq, item.fq};
    end

    `dv_info($sformatf("WDATA size: %d x 8B bank:%0d rcvd_cnt:%0d",
                       obs.fq.size(), bank, cfg.otf_ctrl_wr_rcvd++), UVM_MEDIUM, "process_write")

    compare_data(obs.fq, exp.fq, bank, "wdata");
  endtask // process_eg

  // Compare 64 bit for now
  task compare_data(fdata_q_t obs, exp, int bank, string rw);
    string str = $sformatf("%s_comp_bank%0d", rw, bank);
    bit    err = 0;

    foreach(obs[i]) begin
      if (obs[i][63:0] != exp[i][63:0]) begin
        err = 1;
        `dv_error($sformatf("%4d: obs:exp    %8x_%8x:%8x_%8x  mismatch!!", i,
                  obs[i][63:32], obs[i][31:0], exp[i][63:32], exp[i][31:0]),
                  str)
      end
    end
    if (err == 0) begin
      `dv_info("data match!!", UVM_MEDIUM, str)
    end
  endtask // compare_xdata

endclass
