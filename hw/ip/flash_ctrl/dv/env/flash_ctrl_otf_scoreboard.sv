// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_otf_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(flash_ctrl_otf_scoreboard)
  `uvm_component_new

  // OTF data path fifos
  // Assuming egress (host -> flash) ordering is  maintained per bank.
  uvm_tlm_analysis_fifo #(flash_otf_item) eg_exp_ctrl_fifo[flash_ctrl_pkg::NumBanks];
  uvm_tlm_analysis_fifo #(flash_otf_item) eg_exp_host_fifo[flash_ctrl_pkg::NumBanks];
  uvm_tlm_analysis_fifo #(flash_otf_item) eg_rtl_ctrl_fifo[flash_ctrl_pkg::NumBanks];
  uvm_tlm_analysis_fifo #(flash_otf_item) eg_rtl_host_fifo[flash_ctrl_pkg::NumBanks];
  uvm_tlm_analysis_fifo #(flash_phy_prim_item) eg_rtl_fifo[flash_ctrl_pkg::NumBanks];
  flash_ctrl_env_cfg cfg;
  int dbg1 = 0;
  int dbg2 = 0;

  // Host read cache
  logic [flash_phy_pkg::FullDataWidth-1:0] stage_buf[flash_ctrl_pkg::NumBanks];
  bit[flash_ctrl_pkg::BusAddrByteW-1:0]    stage_addr[flash_ctrl_pkg::NumBanks];

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    foreach(eg_exp_ctrl_fifo[i]) begin
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
    flash_otf_item       exp_ctrl_item[flash_ctrl_pkg::NumBanks];
    flash_otf_item       exp_host_item[flash_ctrl_pkg::NumBanks];
    flash_phy_prim_item  phy_item[flash_ctrl_pkg::NumBanks];
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
    bit[flash_ctrl_pkg::BusAddrByteW-1:0] phy_addr;
    string str = $sformatf("host_read_comp_bank%0d", bank);

    `JDBG(("EXPGET_HOST: addr %x  data:%x   cnt:%0d  rtlff:%0d  xxx:%0d", exp.start_addr, exp.dq[0], dbg1++, eg_rtl_host_fifo[bank].used(), eg_rtl_ctrl_fifo[bank].used()))

    // Check cache with phy address
    phy_addr = exp.start_addr >> 3;

    if (stage_addr[bank] == phy_addr ) begin
      `JDBG(("CACHE%0d: phy_addr:%x exists   data: %x",bank, phy_addr, stage_buf[bank]))
      `uvm_create_obj(flash_otf_item, obs)
      obs.cmd.addr = phy_addr;
      obs.start_addr = phy_addr;
      obs.fq.push_back(stage_buf[bank]);
    end else begin
      eg_rtl_host_fifo[bank].get(obs);
      stage_buf[bank] = obs.fq[0];
      stage_addr[bank] = phy_addr;
    end

    obs.is_direct = 1;
    obs.print("rtl_host: before");
    obs.descramble(exp.addr_key, exp.data_key);
    obs.print("rtl_host: after");
    `JDBG(("SB: rcvd:%0d",cfg.otf_host_rd_sent))

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
    `JDBG(("EXPGET: op:%s fq:%0d dbg:%0d rtlff:%0d", item.cmd.op.name(), item.fq.size(), dbg1++, eg_rtl_ctrl_fifo[bank].used()))
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
    flash_otf_item       obs, item;
    int col_sz = exp.fq.size;
    `JDBG(("process_read:bank:%0d colsz:%0d ffsz:%0d", bank, col_sz, eg_rtl_ctrl_fifo[bank].used()))
    exp.print("exp_read");

    eg_rtl_ctrl_fifo[bank].get(item);
    `uvm_create_obj(flash_otf_item, obs)
    obs = item;

if(bank == 1) begin
   item.printfq(item.fq, "CFF_DBG:OUT:HEAD");
end
     
    repeat(col_sz - 1) begin
      eg_rtl_ctrl_fifo[bank].get(item);
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
    flash_otf_item       obs, item;
    int col_sz = exp.fq.size / 8;

    `JDBG(("process_write:col&comp:bank:%0d colsz:%0d ffsz:%0d", bank, col_sz, eg_rtl_ctrl_fifo[bank].used()))
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
  endtask // compare_data

  // Transform phy_item to otf_item and
  // classify to host or ctrl transaction
  task process_phy_item(flash_phy_prim_item item, int bank);
    flash_otf_item       obs;
if (bank == 1) begin
   `JDBG(("PHY_ITEM: cffsz:%0d   hffsz:%0d",eg_rtl_ctrl_fifo[bank].used(), eg_rtl_host_fifo[bank].used()))
   `JDBG(("PHY_ITEM: addr:%x   data:%x    is_host:%0d",item.req.addr, item.rsp.rdata, item.req.addr[flash_ctrl_pkg::BankAddrW-1]))
end
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
	 if(bank == 1) begin
	    `JDBG(("CFF_DBG:IN cffsz:%0d",eg_rtl_ctrl_fifo[bank].used()))
	    obs.print("CFF_DBG:OBS");
	    
	 end
        eg_rtl_ctrl_fifo[bank].write(obs);
      end
    end

     

  endtask // process_phy_item

endclass
