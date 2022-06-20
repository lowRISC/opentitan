// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_otf_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(flash_ctrl_otf_scoreboard)
  `uvm_component_new

  // OTF data path fifos
  // Assuming egress (host -> flash) ordering is  maintained per bank.
  uvm_tlm_analysis_fifo #(flash_otf_item) eg_exp_ctrl_fifo[NumBanks];
  uvm_tlm_analysis_fifo #(flash_otf_item) eg_exp_host_fifo[NumBanks];
  uvm_tlm_analysis_fifo #(flash_otf_item) eg_rtl_ctrl_fifo[NumBanks];
  uvm_tlm_analysis_fifo #(flash_otf_item) eg_rtl_host_fifo[NumBanks];
  uvm_tlm_analysis_fifo #(flash_phy_prim_item) eg_rtl_fifo[NumBanks];

  flash_ctrl_env_cfg cfg;

  int eg_exp_cnt = 0;

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    foreach (eg_exp_ctrl_fifo[i]) begin
      eg_exp_ctrl_fifo[i] = new($sformatf("eg_exp_ctrl_fifo[%0d]", i), this);
      eg_exp_host_fifo[i] = new($sformatf("eg_exp_host_fifo[%0d]", i), this);
      eg_rtl_ctrl_fifo[i] = new($sformatf("eg_rtl_ctrl_fifo[%0d]", i), this);
      eg_rtl_host_fifo[i] = new($sformatf("eg_rtl_host_fifo[%0d]", i), this);
      eg_rtl_fifo[i] = new($sformatf("eg_rtl_fifo[%0d]", i), this);
    end
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    uvm_config_db#(flash_ctrl_env_cfg)::get(this, "", "cfg", cfg);
  endfunction // connect_phase

  task run_phase(uvm_phase phase);
    flash_otf_item       exp_ctrl_item[NumBanks];
    flash_otf_item       exp_host_item[NumBanks];
    flash_phy_prim_item  phy_item[NumBanks];

    fork
      forever begin
        eg_exp_ctrl_fifo[0].get(exp_ctrl_item[0]);
        process_eg(exp_ctrl_item[0], 0);
      end
      forever begin
        eg_exp_ctrl_fifo[1].get(exp_ctrl_item[1]);
        process_eg(exp_ctrl_item[1], 1);
      end
      forever begin
        eg_exp_host_fifo[0].get(exp_host_item[0]);
        process_eg_host(exp_host_item[0], 0);
      end
      forever begin
        eg_exp_host_fifo[1].get(exp_host_item[1]);
        process_eg_host(exp_host_item[1], 1);
      end
      forever begin
        eg_rtl_fifo[0].get(phy_item[0]);
        process_phy_item(phy_item[0], 0);
      end
      forever begin
        eg_rtl_fifo[1].get(phy_item[1]);
        process_phy_item(phy_item[1], 1);
      end
    join_none
  endtask // run_phase

  task process_eg_host(flash_otf_item exp, int bank);
    flash_otf_item obs;
    data_4s_t rcvd_data;
    fdata_q_t fq;
    string str = $sformatf("host_read_comp_bank%0d", bank);

    `uvm_info("EXPGET_HOST", $sformatf(" addr %x  data:%x   cnt:%0d  rtlff:%0d  xxx:%0d",
                                       exp.start_addr, exp.dq[0], eg_exp_cnt++,
                                       eg_rtl_host_fifo[bank].used(),
                                       eg_rtl_ctrl_fifo[bank].used()),
              UVM_MEDIUM)

    // bankdoor read from memory model
    eg_rtl_host_fifo[bank].get(obs);
    obs.cmd.addr = exp.start_addr; // tl_addr
    // descramble needs 2 buswords
    obs.cmd.addr[2] = 0;
    obs.cmd.num_words = 2;

    obs.print("RAW");
    cfg.flash_mem_bkdr_read(obs.cmd, obs.dq);
    obs.fq = obs.dq2fq(obs.dq);

    obs.is_direct = 1;
    obs.print("rtl_host: before");
    obs.descramble(exp.addr_key, exp.data_key);
    obs.print("rtl_host: after");
    `uvm_info("process_eg_host", $sformatf(" rcvd:%0d",cfg.otf_host_rd_sent), UVM_MEDIUM)

    if (exp.start_addr[2]) begin
       rcvd_data = obs.dq[1];
    end else begin
       rcvd_data = obs.dq[0];
    end

     if (rcvd_data == exp.dq[0]) begin
        `dv_info("data match!!", UVM_MEDIUM, str)
     end else begin
        `dv_error($sformatf(" : obs:exp    %8x:%8x mismatch!!", rcvd_data, exp.dq[0]), str)
     end

    cfg.otf_host_rd_sent++;
  endtask // process_eg_host

  task process_eg(flash_otf_item item, int bank);
    `uvm_info("EG_EXPGET", $sformatf("op:%s fq:%0d cnt:%0d rtlff:%0d", item.cmd.op.name(),
                                     item.fq.size(), eg_exp_cnt++, eg_rtl_fifo[bank].used()),
              UVM_MEDIUM)

    case (item.cmd.op)
      FlashOpProgram:begin
        process_write(item, bank);
      end
      FlashOpRead:begin
        process_read(item, bank);
      end
      default:begin
        // TODO support other commands
      end
    endcase
  endtask

  // Scoreboard process read in following order.
  //   - Received expected transactions (exp).
  //   - Pop the same number (col_sz) of transaction from rtl received q.
  //   - Transform rtl transactions to have the same data format as exp.
  //   - Compare read data.
  task process_read(flash_otf_item exp, int bank);
    flash_otf_item item;
    flash_otf_item obs;
    int col_sz = exp.fq.size;
    `uvm_info("process_read", $sformatf("bank:%0d colsz:%0d ffsz:%0d",
                                        bank, col_sz, eg_rtl_fifo[bank].used()), UVM_HIGH)
    exp.print("exp_read");

    eg_rtl_ctrl_fifo[bank].get(obs);
    obs.cmd = exp.cmd;
    obs.cmd.addr[OTFBankId] = bank;
    obs.cmd.num_words = col_sz * 2;

    obs.print("RAW");
    cfg.flash_mem_bkdr_read(obs.cmd, obs.dq);

    repeat ((2 * col_sz) - 1) begin
      eg_rtl_ctrl_fifo[bank].get(item);
    end

    obs.print("rtl_read: enc_data");
    obs.fq = obs.dq2fq(obs.dq);

    obs.descramble(exp.addr_key, exp.data_key);
    obs.print("rtl_read: raw_data");
    `dv_info($sformatf("RDATA size: %d x 8B bank:%0d sent_cnt:%0d",
                       obs.raw_fq.size(), bank, cfg.otf_ctrl_rd_sent++),
             UVM_MEDIUM, "process_read")
    compare_data(obs.raw_fq, exp.fq, bank, "rdata");
  endtask

  // Scoreboard process write in following order.
  //   - Received expected transactions (exp).
  //   - Pop the same number (col_sz) of transaction from rtl received q.
  //   - Transform rtl transactions to have the same data format as exp.
  //   - Compare read data.
  task process_write(flash_otf_item exp, int bank);
    flash_otf_item item;
    flash_otf_item obs;

    // Write transactions coalesce upto 8 transactions.
    // So each pop becomes 8 times of fqs.
    int col_sz = exp.fq.size / 8;
    `uvm_info("process_write", $sformatf("process_write:col&comp:bank:%0d colsz:%0d ffsz:%0d",
                                         bank, col_sz, eg_rtl_ctrl_fifo[bank].used()), UVM_HIGH)
    eg_rtl_ctrl_fifo[bank].get(item);
    `uvm_create_obj(flash_otf_item, obs)
    obs = item;

    repeat(col_sz - 1) begin
      eg_rtl_ctrl_fifo[bank].get(item);
      obs.fq = {obs.fq, item.fq};
    end

    `dv_info($sformatf("WDATA size: %d x 8B bank:%0d rcvd_cnt:%0d",
                       obs.fq.size(), bank, cfg.otf_ctrl_wr_rcvd++), UVM_MEDIUM, "process_write")

    compare_data(obs.fq, exp.fq, bank, "wdata");
  endtask // process_eg

  // Compare 64 bit for now
  task compare_data(fdata_q_t obs, fdata_q_t exp, int bank, string rw);
    string str = $sformatf("%s_comp_bank%0d", rw, bank);
    bit    err = 0;

    foreach (obs[i]) begin
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
  endtask // compare_data

  // Transform phy_item to otf_item and
  // classify to host or ctrl transaction
  task process_phy_item(flash_phy_prim_item item, int bank);
    flash_otf_item       obs;
    `uvm_create_obj(flash_otf_item, obs);
    if (item.req.prog_req) begin
      obs.get_from_phy(item, "w");
      eg_rtl_ctrl_fifo[bank].write(obs);
    end else begin // read request, guaranteed by monitor
      obs.get_from_phy(item, "r");
      if (item.req.addr[flash_ctrl_pkg::BankAddrW-1]) begin // host read
        obs.start_addr = obs.cmd.addr;
        eg_rtl_host_fifo[bank].write(obs);
      end else begin // ctrl read
        eg_rtl_ctrl_fifo[bank].write(obs);
      end
    end
  endtask // process_phy_item
endclass
