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

  // Check last mile write /erase transactions
  uvm_tlm_analysis_fifo #(flash_phy_prim_item) eg_exp_lm_fifo[NumBanks];

  // tb memory model
  // This is used for the last mile write data integrity check
  bit[flash_phy_pkg::FullDataWidth-1:0] data_mem[NumBanks][bit[BankAddrW-1:0]];
  bit[flash_phy_pkg::FullDataWidth-1:0] info_mem[NumBanks][InfoTypes][bit[BankAddrW-1:0]];

  // register double written entries
  bit corrupt_entry[rd_cache_t];
  flash_ctrl_env_cfg cfg;

  int eg_exp_cnt = 0;
  bit comp_off = 0;
  bit derr_expected = 0;

  // monitor_tb_mem off
  bit mem_mon_off = 0;

  // Stop egress forever process
  bit stop = 0;

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    foreach (eg_exp_ctrl_fifo[i]) begin
      eg_exp_ctrl_fifo[i] = new($sformatf("eg_exp_ctrl_fifo[%0d]", i), this);
      eg_exp_host_fifo[i] = new($sformatf("eg_exp_host_fifo[%0d]", i), this);
      eg_rtl_ctrl_fifo[i] = new($sformatf("eg_rtl_ctrl_fifo[%0d]", i), this);
      eg_rtl_host_fifo[i] = new($sformatf("eg_rtl_host_fifo[%0d]", i), this);
      eg_rtl_fifo[i] = new($sformatf("eg_rtl_fifo[%0d]", i), this);
      rd_cmd_fifo[i] = new($sformatf("rd_cmd_fifo[%0d]", i), this);
      eg_exp_lm_fifo[i] = new($sformatf("eg_exp_lm_fifo[%0d]", i), this);
    end
  endfunction

  task clear_fifos();
    flash_otf_item dummy1;
    flash_phy_prim_item dummy2;

    foreach (eg_exp_ctrl_fifo[i]) begin
      while (eg_exp_ctrl_fifo[i].used() > 0) eg_exp_ctrl_fifo[i].get(dummy1);
      while (eg_exp_host_fifo[i].used() > 0) eg_exp_host_fifo[i].get(dummy1);
      while (eg_rtl_ctrl_fifo[i].used() > 0) eg_rtl_ctrl_fifo[i].get(dummy1);
      while (eg_rtl_host_fifo[i].used() > 0) eg_rtl_host_fifo[i].get(dummy1);
      while (eg_rtl_fifo[i].used() > 0) eg_rtl_fifo[i].get(dummy2);
      while (rd_cmd_fifo[i].used() > 0) rd_cmd_fifo[i].get(dummy2);
      while (eg_exp_lm_fifo[i].used() > 0) eg_exp_lm_fifo[i].get(dummy2);
    end
  endtask

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    uvm_config_db#(flash_ctrl_env_cfg)::get(this, "", "cfg", cfg);
    cfg.otf_scb_h = this;
  endfunction // connect_phase

  task run_phase(uvm_phase phase);
    flash_otf_item       exp_ctrl_item[NumBanks];
    flash_otf_item       exp_host_item[NumBanks];
    flash_phy_prim_item  phy_item[NumBanks];
    flash_phy_prim_item  rcmd[NumBanks];

    for (int i = 0; i < NumBanks; i++) begin
      int j = i;
      fork begin
        forever begin
          eg_exp_ctrl_fifo[j].get(exp_ctrl_item[j]);
          process_eg(exp_ctrl_item[j], j);
        end
      end join_none
      fork begin
        forever begin
          eg_exp_host_fifo[j].get(exp_host_item[j]);
          process_eg_host(exp_host_item[j], j);
        end
      end join_none
      fork begin
        forever begin
          eg_rtl_fifo[j].get(phy_item[j]);
          process_phy_item(phy_item[j], j);
        end
      end join_none
      fork begin
        forever begin
          rd_cmd_fifo[j].get(rcmd[j]);
          process_rcmd(rcmd[j], j);
        end
      end join_none
      fork begin
        monitor_tb_mem(j);
      end join_none
    end
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
    obs.skip_err_chk |= exp.derr;

    // descramble needs 2 buswords
    obs.cmd.num_words = 2;
    obs.descramble(exp.addr_key, exp.data_key);
    obs.print("rtl_host: after");
    `uvm_info("process_eg_host", $sformatf(" rcvd:%0d",cfg.otf_host_rd_sent), UVM_MEDIUM)

    if (cfg.ecc_mode > FlashSerrTestMode && obs.derr == 1) begin
      err_addr = {obs.cmd.addr[31:3],3'h0};
      // check expected derr
      if (cfg.derr_addr_tbl[err_addr].exists(FlashPartData)) begin
        `uvm_info("process_eg_host",
                  $sformatf("expected double bit error 0x%x", err_addr), UVM_MEDIUM)
      end else if (cfg.ierr_addr_tbl[err_addr].exists(FlashPartData)) begin
        `uvm_info("process_eg_host",
                  $sformatf("expected icv error 0x%x", err_addr), UVM_MEDIUM)
      end else begin
        `uvm_error("process_eg_host",
                   $sformatf("unexpected double bit error 0x%x", err_addr))
      end
    end else begin
      if (exp.exp_err) begin
        `uvm_info("process_eg_host",
                  $sformatf("expected other tlul error start:%x",
                            exp.start_addr),
                  UVM_MEDIUM)
      end else if (exp.derr & obs.derr) begin
        `uvm_info("process_eg_host",
                  $sformatf("expected double bit error by redundant write start:%x",
                            exp.start_addr),
                  UVM_MEDIUM)
      end else begin
        if (!exp.derr) begin
          if (exp.start_addr[2]) begin
            rcvd_data = obs.dq[1];
          end else begin
            rcvd_data = obs.dq[0];
          end

          if (rcvd_data == exp.dq[0]) begin
            `dv_info("data match!!", UVM_MEDIUM, str)
          end else begin
            `dv_error($sformatf(" : obs:exp    %8x:%8x mismatch!!",
                                rcvd_data, exp.dq[0]), str)
          end
        end else begin // if (!exp.derr)
          `uvm_error("process_eg_host",
                     $sformatf("expected double bit error does not occur start:%x",
                               exp.start_addr))
        end
      end
    end
    cfg.otf_host_rd_sent++;

  endtask // process_eg_host

  task process_eg(flash_otf_item item, int bank);
    `uvm_info("EG_EXPGET",
              $sformatf("op:%s fq:%0d cnt:%0d rtlff:%0d", item.cmd.op.name(),
                        item.fq.size(), eg_exp_cnt++, eg_rtl_fifo[bank].used()),
              UVM_MEDIUM)
    fork
      begin : isolation_fork
        fork
          begin
            case (item.cmd.op)
              FlashOpProgram:begin
                process_write(item, bank);
              end
              FlashOpRead:begin
                process_read(item, bank);
              end
              default:begin
                // Do nothing for the other commands
              end
            endcase // case (item.cmd.op)
          end // fork begin
          begin
            wait (stop);
          end
        join_any
        #0;
        disable fork;
      end // block: isolation_fork
    join
  endtask

  // Scoreboard process read in following order.
  //   - Received expected transactions (exp).
  //   - Pop the same number (col_sz) of transaction from rtl received q.
  //   - Transform rtl transactions to have the same data format as exp.
  //   - Compare read data.
  task process_read(flash_otf_item exp, int bank);
    flash_otf_item send;
    addr_t err_addr, cp_addr;
    int page;
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
    if (cfg.ecc_mode > FlashSerrTestMode) send.skip_err_chk = 1;
    send.skip_err_chk |= exp.derr;

    if (exp.cmd.addr[2]) begin
      send.head_pad = 1;
      send.cmd.num_words++;
    end
    if (send.cmd.num_words % 2) begin
      send.cmd.num_words++;
      send.tail_pad = 1;
    end

    // Read descramble has to be done Qword by Qword because
    // Each Qword can be in different region.
    send.mem_addr = exp.start_addr >> 3;
    send.ctrl_rd_region_q = exp.ctrl_rd_region_q;

    send.descramble(exp.addr_key, exp.data_key);
    send.print("exp_read: raw_data");
    `dv_info($sformatf("RDATA size: %d x 8B bank:%0d sent_cnt:%0d",
                       send.raw_fq.size(), bank, cfg.otf_ctrl_rd_sent++),
             UVM_MEDIUM, "process_read")

    if (cfg.ecc_mode > FlashSerrTestMode && send.derr == 1) begin
      foreach(send.eaddr_q[i]) begin
        err_addr = send.eaddr_q[i];
        err_addr[OTFBankId] = bank;

        // check expected derr
        if (cfg.derr_addr_tbl[err_addr].exists(exp.cmd.partition)) begin
          `uvm_info("process_read",
                    $sformatf("expected double bit error 0x%x", err_addr), UVM_MEDIUM)
        end else if (cfg.ierr_addr_tbl[err_addr].exists(exp.cmd.partition)) begin
          `uvm_info("process_read",
                    $sformatf("expected icv error 0x%x", err_addr), UVM_MEDIUM)
        end else if (derr_expected == 0) begin
          `uvm_error("process_read",
                     $sformatf("unexpected double bit error 0x%x", err_addr))
        end
      end
    end else begin // if (cfg.ecc_mode > FlashSerrTestMode && send.derr == 1)
      // Skip data comp for no ecc erase workd read
      foreach (send.ctrl_rd_region_q[i]) begin
        if (send.ctrl_rd_region_q[i].ecc_en != MuBi4True &&
            (exp.fq[i][63:32] == ALL_ONES || exp.fq[i][31:0] == ALL_ONES)) begin
          send.raw_fq[i] = exp.fq[i];
        end
      end
      if (exp.exp_err) begin
        `uvm_info("process_read",
                  $sformatf("expected other tlul error start:%x",
                            exp.start_addr),
                  UVM_MEDIUM)
      end else if (exp.derr & send.derr) begin
        `uvm_info("process_read",
                  $sformatf("expected double bit error by redundant write start:%x",
                            exp.start_addr),
                  UVM_MEDIUM)
      end else begin
        if (!exp.derr) compare_data(send.raw_fq, exp.fq, bank, "rdata");
        else `uvm_error("process_read",
                        $sformatf("expected double bit error does not occur start:%x",
                                  exp.start_addr))

      end
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

    // Fatal alert from host interface can disturb core tlul
    if (cfg.scb_h.alert_count["fatal_err"]) begin
       `uvm_info(`gfn, "comparison skipped due to fatal error is detected", UVM_MEDIUM)
       return;
    end
    if (comp_off) return;

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
    flash_dv_part_e part = get_part_name(item.req);
    if (cfg.ecc_mode == FlashSerrTestMode) begin
      serr_addr = item.req.addr << 3;
      serr_addr[OTFBankId] = bank;
      if (cfg.serr_addr_tbl[serr_addr].exists(part)) begin
        cfg.inc_serr_cnt(bank);
        cfg.serr_addr[bank] = serr_addr;
      end
    end
  endtask

  task monitor_tb_mem(int bank);
    flash_phy_prim_item exp;
    flash_otf_mem_entry rcv;
    string name = $sformatf("mon_tb_mem%0d", bank);
    forever begin
      @(posedge cfg.flash_ctrl_mem_vif[bank].mem_wr);
      if (mem_mon_off == 0) begin
        `uvm_info("mem_if", "got posedge wr", UVM_MEDIUM)
        `uvm_create_obj(flash_otf_mem_entry, rcv)
        #1ps;
        rcv.mem_addr = cfg.flash_ctrl_mem_vif[bank].mem_addr;
        rcv.mem_wdata = cfg.flash_ctrl_mem_vif[bank].mem_wdata;
        rcv.mem_part = cfg.flash_ctrl_mem_vif[bank].mem_part;
        rcv.mem_info_sel = cfg.flash_ctrl_mem_vif[bank].mem_info_sel;
        @(negedge cfg.flash_ctrl_mem_vif[bank].clk_i);
        if (cfg.seq_cfg.use_vendor_flash == 0) begin
          if (rcv.mem_part == FlashPartData) begin
            `DV_CHECK_EQ(cfg.flash_ctrl_mem_vif[bank].data_mem_req, 1,,, name)
          end else begin
            case (rcv.mem_info_sel)
              0: `DV_CHECK_EQ(cfg.flash_ctrl_mem_vif[bank].info0_mem_req, 1,,, name)
              1: `DV_CHECK_EQ(cfg.flash_ctrl_mem_vif[bank].info1_mem_req, 1,,, name)
              2: `DV_CHECK_EQ(cfg.flash_ctrl_mem_vif[bank].info2_mem_req, 1,,, name)
              default: `uvm_error(name, $sformatf("bank%0d infosel%0d doesn't exists",
                                                  bank, rcv.mem_info_sel))
            endcase
          end
        end
        // collect ref data
        eg_exp_lm_fifo[bank].get(exp);
        lm_wdata_comp(exp, rcv, bank);
      end
    end
  endtask // monitor_tb_mem

  task lm_wdata_comp(flash_phy_prim_item exp, flash_otf_mem_entry rcv, int bank);
    bit[flash_phy_pkg::FullDataWidth] rd_data;
    rd_cache_t entry;
    string name = $sformatf("lm_wdata_comp_bank%0d", bank);

    if (rcv.mem_addr == exp.req.addr) begin
      `dv_info($sformatf("addr match %x", rcv.mem_addr), UVM_MEDIUM, name)
    end else begin
      `DV_CHECK_EQ(rcv.mem_addr, exp.req.addr,,, name)
    end

   // check if this is page erase
    if (exp.req.pg_erase_req | exp.req.bk_erase_req) begin
      int cnt = 0;
      int cnt_max = (exp.req.bk_erase_req)? 65536 : 256;

      `uvm_info(name, $sformatf("erase detected  pg_erase:%0d bk_erase:%0d",
                                exp.req.pg_erase_req, exp.req.bk_erase_req),
                UVM_MEDIUM)
      repeat (cnt_max) begin
        rcv.mem_addr = cfg.flash_ctrl_mem_vif[bank].mem_addr;
        rcv.mem_wdata = cfg.flash_ctrl_mem_vif[bank].mem_wdata;
        rcv.mem_part = cfg.flash_ctrl_mem_vif[bank].mem_part;
        rcv.mem_info_sel = cfg.flash_ctrl_mem_vif[bank].mem_info_sel;

        entry.bank = bank;
        entry.addr = (rcv.mem_addr<<3);
        entry.part = cfg.get_part(rcv.mem_part, rcv.mem_info_sel);
        corrupt_entry.delete(entry);

        if (rcv.mem_addr == exp.req.addr) begin
          `dv_info($sformatf("addr match %x", rcv.mem_addr), UVM_MEDIUM, name)
        end else begin
          `DV_CHECK_EQ(rcv.mem_addr, exp.req.addr,,, name)
        end
        `DV_CHECK_EQ(rcv.mem_wdata, {flash_phy_pkg::FullDataWidth{1'b1}},,, name)


        if (rcv.mem_part == FlashPartData) begin
          data_mem[bank].delete(rcv.mem_addr);
        end else begin
          info_mem[bank][rcv.mem_info_sel].delete(rcv.mem_addr);
        end
        exp.req.addr++;
        @(negedge cfg.flash_ctrl_mem_vif[bank].clk_i);
      end
   end else begin
     bit skip_comp = 0;
     entry.bank = bank;
     entry.addr = (rcv.mem_addr<<3);
     entry.part = cfg.get_part(rcv.mem_part, rcv.mem_info_sel);

     if (rcv.mem_part == FlashPartData) begin
       if (data_mem[bank].exists(rcv.mem_addr)) begin
         corrupt_entry[entry] = 1;
         rd_data = data_mem[bank][rcv.mem_addr];
         if (cfg.seq_cfg.use_vendor_flash == 0) begin
           exp.req.prog_full_data &= rd_data;
         end else begin
           skip_comp = 1;
         end
         data_mem[bank].delete(rcv.mem_addr);
       end
       data_mem[bank][rcv.mem_addr] = exp.req.prog_full_data;
     end else begin
        `uvm_info(`gfn, $sformatf("bank:%0d sel:%0d addr:%x",
                                  bank, rcv.mem_info_sel, rcv.mem_addr), UVM_HIGH)
        `uvm_info(`gfn, $sformatf("scb_rd_data:%x prog_data:%x",
             info_mem[bank][rcv.mem_info_sel][rcv.mem_addr], exp.req.prog_full_data), UVM_HIGH)
       if (info_mem[bank][rcv.mem_info_sel].exists(rcv.mem_addr)) begin
         corrupt_entry[entry] = 1;
         rd_data = info_mem[bank][rcv.mem_info_sel][rcv.mem_addr];
         if (cfg.seq_cfg.use_vendor_flash == 0) begin
           exp.req.prog_full_data &= rd_data;
         end else begin
           skip_comp = 1;
         end
         info_mem[bank][rcv.mem_info_sel].delete(rcv.mem_addr);
       end
       info_mem[bank][rcv.mem_info_sel][rcv.mem_addr] = exp.req.prog_full_data;
     end

     if (rcv.mem_wdata == exp.req.prog_full_data) begin
       `dv_info($sformatf("wdata match %x", rcv.mem_wdata), UVM_MEDIUM, name)
     end else begin
       if (!skip_comp) begin
         `DV_CHECK_EQ(rcv.mem_wdata, exp.req.prog_full_data,,, name)
       end
     end
   end
  endtask // lm_wdata_cmp
endclass
