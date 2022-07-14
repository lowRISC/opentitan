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
  uvm_tlm_analysis_fifo #(flash_phy_prim_item) rd_cmd_fifo[NumBanks];

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
      rd_cmd_fifo[i] = new($sformatf("rd_cmd_fifo[%0d]", i), this);
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
    flash_phy_prim_item  rcmd[NumBanks];

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
      forever begin
        rd_cmd_fifo[0].get(rcmd[0]);
        process_rcmd(rcmd[0], 0);
      end
      forever begin
        rd_cmd_fifo[1].get(rcmd[1]);
        process_rcmd(rcmd[1], 1);
      end
    join_none
  endtask // run_phase

  task process_eg_host(flash_otf_item exp, int bank);
    flash_otf_item obs;
    data_4s_t rcvd_data;
    fdata_q_t fq;
    addr_t err_addr;
    string str = $sformatf("host_read_comp_bank%0d", bank);

    `uvm_info("EXPGET_HOST", $sformatf(" addr %x  data:%x   cnt:%0d  rtlff:%0d  ctrlff:%0d",
                                       exp.start_addr, exp.dq[0], eg_exp_cnt++,
                                       eg_rtl_host_fifo[bank].used(),
                                       eg_rtl_ctrl_fifo[bank].used()),
                                       UVM_MEDIUM)

    // bankdoor read from memory model
    `uvm_create_obj(flash_otf_item, obs)
    // Host can only access data partitions.
    obs.cmd.partition = FlashPartData;
    obs.cmd.op = FlashOpRead;
    obs.cmd.addr = exp.start_addr; // tl_addr
    // for debug print
    obs.start_addr = exp.start_addr;
    obs.cmd.num_words = 1;
    obs.mem_addr = exp.start_addr >> 3;

    obs.print("RAW");
    cfg.flash_mem_otf_read(obs.cmd, obs.fq);

    obs.print("rtl_host: before");
    obs.region = exp.region;
    if (cfg.ecc_mode > FlashSerrTestMode) obs.skip_err_chk = 1;
    // descramble needs 2 buswords
    obs.cmd.num_words = 2;
    obs.descramble(exp.addr_key, exp.data_key);
    obs.print("rtl_host: after");
    `uvm_info("process_eg_host", $sformatf(" rcvd:%0d",cfg.otf_host_rd_sent), UVM_MEDIUM)

    if (cfg.ecc_mode > FlashSerrTestMode && obs.derr == 1) begin
      err_addr = {obs.cmd.addr[31:3],3'h0};
      // check expected derr
      if (cfg.derr_addr_tbl.exists(err_addr)) begin
        `uvm_info("process_eg_host",
                  $sformatf("expected double bit error 0x%x", err_addr), UVM_MEDIUM)
      end else if (cfg.ierr_addr_tbl.exists(err_addr)) begin
        `uvm_info("process_eg_host",
                  $sformatf("expected icv error 0x%x", err_addr), UVM_MEDIUM)
      end else begin
        `uvm_error("process_eg_host",
                   $sformatf("unexpected double bit error 0x%x", err_addr))
      end
    end else begin
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
    end
    cfg.otf_host_rd_sent++;
  endtask // process_eg_host

  task process_eg(flash_otf_item item, int bank);
    `uvm_info("EG_EXPGET",
              $sformatf("op:%s fq:%0d cnt:%0d rtlff:%0d", item.cmd.op.name(),
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
    flash_otf_item send;
    addr_t err_addr;
    int col_sz = exp.fq.size;
    `uvm_info("process_read", $sformatf("bank:%0d colsz:%0d ffsz:%0d",
                                        bank, col_sz, eg_rtl_fifo[bank].used()), UVM_MEDIUM)

    exp.print("obs_read");
    `uvm_create_obj(flash_otf_item, send)
    send.cmd = exp.cmd;
    send.cmd.addr[OTFBankId] = bank;
    // print purpose
    send.start_addr = exp.start_addr;
    cfg.flash_mem_otf_read(send.cmd, send.fq);
    send.print("exp_read: enc_data");

    if (exp.cmd.addr[2]) begin
      send.head_pad = 1;
      send.cmd.num_words++;
    end
    if (send.cmd.num_words % 2) begin
      send.cmd.num_words++;
      send.tail_pad = 1;
    end
    send.mem_addr = exp.start_addr >> 3;
    send.region = exp.region;

    if (cfg.ecc_mode > FlashSerrTestMode) send.skip_err_chk = 1;
    send.descramble(exp.addr_key, exp.data_key);
    send.print("exp_read: raw_data");
    `dv_info($sformatf("RDATA size: %d x 8B bank:%0d sent_cnt:%0d",
                       send.raw_fq.size(), bank, cfg.otf_ctrl_rd_sent++),
             UVM_MEDIUM, "process_read")

    if (cfg.ecc_mode > FlashSerrTestMode && send.derr == 1) begin
      send.err_addr[OTFBankId] = bank;

      // check expected derr
      if (cfg.derr_addr_tbl.exists(send.err_addr)) begin
        `uvm_info("process_read",
                  $sformatf("expected double bit error 0x%x", send.err_addr), UVM_MEDIUM)
      end else if (cfg.ierr_addr_tbl.exists(send.err_addr)) begin
        `uvm_info("process_read",
                  $sformatf("expected icv error 0x%x", send.err_addr), UVM_MEDIUM)
      end else begin
        `uvm_error("process_read",
                   $sformatf("unexpected double bit error 0x%x", send.err_addr))
      end
    end else begin
      compare_data(send.raw_fq, exp.fq, bank, "rdata");
    end
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
    `uvm_info("process_write", $sformatf("process_write: addr:0x%x bank:%0d colsz:%0d ffsz:%0d",
                       exp.cmd.otf_addr, bank, col_sz, eg_rtl_ctrl_fifo[bank].used()), UVM_MEDIUM)
    eg_rtl_ctrl_fifo[bank].get(item);
    `uvm_create_obj(flash_otf_item, obs)
    obs = item;

    repeat(col_sz - 1) begin
      eg_rtl_ctrl_fifo[bank].get(item);
      obs.fq = {obs.fq, item.fq};
    end

    `dv_info($sformatf("WDATA size: %d x 8B bank:%0d rcvd_cnt:%0d",
                       obs.fq.size(), bank, cfg.otf_ctrl_wr_rcvd++), UVM_MEDIUM, "process_write")

    compare_data(obs.fq, exp.fq, bank, $sformatf("wdata_page%0d", exp.page), exp.ecc_en);
  endtask // process_eg

  // Compare 64 bit for now
  task compare_data(fdata_q_t obs, fdata_q_t exp, int bank, string rw, bit is_ecc = 0);
    string str = $sformatf("%s_comp_bank%0d", rw, bank);
    bit    err = 0;

    foreach (obs[i]) begin
      if(is_ecc) begin
        if (obs[i] != exp[i]) begin
          err = 1;
          `dv_error($sformatf("%4d: obs:exp    %2x_%1x_%8x_%8x:%2x_%1x_%8x_%8x  mismatch!!", i,
                              obs[i][75:68], obs[i][67:64], obs[i][63:32], obs[i][31:0],
                              exp[i][75:68], exp[i][67:64], exp[i][63:32], exp[i][31:0]),
                    str)
        end
      end else begin
        if (obs[i][63:0] != exp[i][63:0]) begin
          err = 1;
          `dv_error($sformatf("%4d: obs:exp    %8x_%8x:%8x_%8x  mismatch!!", i,
                              obs[i][63:32], obs[i][31:0], exp[i][63:32], exp[i][31:0]),
                    str)
        end
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
    end
  endtask // process_phy_item

  task process_rcmd(flash_phy_prim_item item, int bank);
    addr_t serr_addr;
    if (cfg.ecc_mode == FlashSerrTestMode) begin
      serr_addr = item.req.addr << 3;
      serr_addr[OTFBankId] = bank;
      if (cfg.serr_addr_tbl.exists(serr_addr)) begin
        cfg.inc_serr_cnt(bank);
        cfg.serr_addr[bank] = serr_addr;
      end
    end
  endtask
endclass
