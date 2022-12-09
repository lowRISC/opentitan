// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_scoreboard extends cip_base_scoreboard #(
    .CFG_T(i2c_env_cfg),
    .RAL_T(i2c_reg_block),
    .COV_T(i2c_env_cov)
  );
  `uvm_component_utils(i2c_scoreboard)

  virtual i2c_if  i2c_vif;

  local i2c_item  exp_rd_item;
  local i2c_item  exp_wr_item;
  local i2c_item  obs_wr_item;
  local i2c_item  obs_rd_item;
  local i2c_item  rd_pending_item;
  local uint      rd_wait;
  local bit       host_init = 1'b0;
  local uint      rdata_cnt = 0;
  local uint      tran_id = 0;
  local uint      num_exp_tran = 0;

  // queues hold expected read and write transactions
  local i2c_item  exp_wr_q[$];
  local i2c_item  exp_rd_q[$];

  // queues hold partial read transactions (address phase)
  local i2c_item  rd_pending_q[$];

  // TLM fifos hold the transactions sent by monitor
  uvm_tlm_analysis_fifo #(i2c_item) rd_item_fifo;
  uvm_tlm_analysis_fifo #(i2c_item) wr_item_fifo;

  uvm_analysis_port #(i2c_item) target_mode_wr_obs_port;

  // Target mode transactions
  uvm_tlm_analysis_fifo #(i2c_item) target_mode_wr_exp_fifo;
  uvm_tlm_analysis_fifo #(i2c_item) target_mode_wr_obs_fifo;
  uvm_tlm_analysis_fifo #(i2c_item) target_mode_rd_exp_fifo;
  uvm_tlm_analysis_fifo #(i2c_item) target_mode_rd_obs_fifo;

  // interrupt bit vector
  local bit [NumI2cIntr-1:0] intr_exp;

  int                        num_obs_rd;
  int                        obs_wr_id = 0;
  // used only for fifo_reset test
  bit                        skip_acq_comp = 0;
  // Target mode read data is created by fetch_txn.
  // In random tx fifo flush event, this make difficult to chekc read path integrity.
  // With setting this bit, expected read data collected right at the input of tx fifo
  // and at the tx fifo reset event, expected read data also get flushed.
  bit                        read_rnd_data = 0;
  bit [7:0]                  mirrored_txdata[$];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    rd_item_fifo = new("rd_item_fifo", this);
    wr_item_fifo = new("wr_item_fifo", this);
    rd_pending_item = new("rd_pending_item" );
    exp_rd_item = new("exp_rd_item");
    exp_wr_item = new("exp_wr_item");
    obs_wr_item = new("obs_wr_item");
    target_mode_wr_exp_fifo = new("target_mode_wr_exp_fifo", this);
    target_mode_wr_obs_fifo = new("target_mode_wr_obs_fifo", this);
    target_mode_rd_exp_fifo = new("target_mode_rd_exp_fifo", this);
    target_mode_rd_obs_fifo = new("target_mode_rd_obs_fifo", this);
    target_mode_wr_obs_port = new("target_mode_wr_obs_port", this);
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    target_mode_wr_obs_port.connect(target_mode_wr_obs_fifo.analysis_export);
    cfg.scb_h = this;
  endfunction

  task run_phase(uvm_phase phase);
    string str;
    super.run_phase(phase);
    if (cfg.m_i2c_agent_cfg.if_mode == Host) begin
      fork
        forever begin
          fork begin
            fork
              begin
                target_mode_wr_obs_fifo.get(obs_wr_item);
                obs_wr_item.tran_id = obs_wr_id++;
                target_mode_wr_exp_fifo.get(exp_wr_item);
                str = (exp_wr_item.start) ? "addr" : (exp_wr_item.stop) ? "stop" : "wr";
                `uvm_info(`gfn, $sformatf("exp_%s_txn %0d\n %s", str,
                                          exp_wr_item.tran_id, exp_wr_item.sprint()), UVM_MEDIUM)
                target_txn_comp(obs_wr_item, exp_wr_item, str);
              end
              begin
                wait(skip_acq_comp);
                cfg.clk_rst_vif.wait_clks(1);
              end
            join_any
            disable fork;
          end join
        end
        forever begin
          target_mode_rd_obs_fifo.get(obs_rd_item);
          obs_rd_item.pname = "obs_rd";
          obs_rd_item.tran_id = num_obs_rd++;
          if (read_rnd_data) begin
            // With read_rnd_data mode, only read data can be compared.
            // Other variables cannot be predictable.
            `uvm_create_obj(i2c_item, exp_rd_item);
            exp_rd_item.tran_id = obs_rd_item.tran_id;
            exp_rd_item.num_data = obs_rd_item.num_data;
            repeat (exp_rd_item.num_data) begin
              exp_rd_item.data_q.push_back(mirrored_txdata.pop_front);
            end
          end else begin
            target_mode_rd_exp_fifo.get(exp_rd_item);
          end
          exp_rd_item.pname = "exp_rd";
          `uvm_info(`gfn, $sformatf("\n%s", exp_rd_item.convert2string()), UVM_MEDIUM)
          target_rd_comp(obs_rd_item, exp_rd_item);
        end
      join_none
    end else begin
      forever begin
        `DV_SPINWAIT_EXIT(
          fork
            compare_trans(BusOpWrite);
            compare_trans(BusOpRead);
          join,
          @(negedge cfg.clk_rst_vif.rst_n),
        )
      end
    end
  endtask : run_phase

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg   csr;
    i2c_item  sb_exp_wr_item;
    i2c_item  sb_exp_rd_item;
    i2c_item  temp_item;
    bit       fmt_overflow;
    bit       do_read_check = 1'b1;
    bit       write = item.is_write();

    bit addr_phase_write  = (write && channel  == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);

    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("\naccess unexpected addr 0x%0h", csr_addr))
    end

    sb_exp_wr_item = new();
    sb_exp_rd_item = new();
    if (addr_phase_write) begin
      // incoming access is a write to a valid csr, then make updates right away
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));

      // process the csr req
      // for write, update local variable and fifo at address phase
      // for read, update predication at address phase and compare at data phase
      case (csr.get_name())
        // add individual case item for each csr
        "ctrl": begin
          host_init = ral.ctrl.enablehost.get_mirrored_value();
        end
        "fdata": begin
          bit [7:0] fbyte;
          bit start, stop, read, rcont, nakok;

          if (!cfg.under_reset && host_init) begin
            fbyte = get_field_val(ral.fdata.fbyte, item.a_data);
            start = bit'(get_field_val(ral.fdata.start, item.a_data));
            stop  = bit'(get_field_val(ral.fdata.stop, item.a_data));
            read  = bit'(get_field_val(ral.fdata.read, item.a_data));
            rcont = bit'(get_field_val(ral.fdata.rcont, item.a_data));
            nakok = bit'(get_field_val(ral.fdata.nakok, item.a_data));

            // target address is begin programmed to begin a transaction
            if (start) begin
              tran_id++;
              if (exp_wr_item.start && !sb_exp_wr_item.stop &&
                  exp_wr_item.bus_op == BusOpWrite) begin
                // write transaction ends with rstart
                exp_wr_item.rstart = 1'b1;
                `downcast(sb_exp_wr_item, exp_wr_item.clone());
                sb_exp_wr_item.stop = 1'b1;
                exp_wr_item.clear_all();
              end
              if (fbyte[0]) begin
                // read transaction
                exp_rd_item.tran_id = tran_id;
                exp_rd_item.bus_op  = BusOpRead;
                exp_rd_item.addr    = fbyte[7:1];
                exp_rd_item.start   = start;
                exp_rd_item.stop    = stop;
              end else begin
                // write transaction
                exp_wr_item.tran_id = tran_id;
                exp_wr_item.bus_op  = BusOpWrite;
                exp_wr_item.addr    = fbyte[7:1];
                exp_wr_item.start   = start;
                exp_wr_item.stop    = stop;
              end
            end else begin // transaction begins with started/rstarted
              // write transaction
              if (exp_wr_item.start && exp_wr_item.bus_op == BusOpWrite) begin
                // irq is asserted with 2 latency cycles (#3422)
                cfg.clk_rst_vif.wait_clks(2);
                // TODO: Gather all irq verification in SCB instead of distribute in vseq
                if (cfg.intr_vif.pins[FmtOverflow]) begin
                  exp_wr_item.fmt_ovf_data_q.push_back(fbyte);
                  //wait(!cfg.intr_vif.pins[FmtOverflow]);
                end else begin
                  // fmt_fifo is underflow then collect data, otherwise drop data
                  exp_wr_item.data_q.push_back(fbyte);
                  exp_wr_item.num_data++;
                  exp_wr_item.stop = stop;
                  if (exp_wr_item.stop) begin
                    // get a complete write
                    `downcast(sb_exp_wr_item, exp_wr_item.clone());
                    exp_wr_item.clear_all();
                  end
                end
              end
              // read transaction
              if (exp_rd_item.start && exp_rd_item.bus_op == BusOpRead) begin
                if (read) begin
                  i2c_item tmp_rd_item;
                  uint num_rd_bytes = (fbyte == 8'd0) ? 256 : fbyte;
                  // get the number of byte to read
                  if (exp_rd_item.rcont && (rcont || stop)) begin
                    exp_rd_item.num_data += num_rd_bytes; // accumulate for chained reads
                  end else begin
                    exp_rd_item.num_data  = num_rd_bytes;
                  end
                  exp_rd_item.stop   = stop;
                  exp_rd_item.rcont  = rcont;
                  exp_rd_item.read   = read;
                  exp_rd_item.nakok  = nakok;
                  exp_rd_item.nack   = ~exp_rd_item.rcont;
                  exp_rd_item.rstart = (exp_rd_item.stop) ? 1'b0 : 1'b1;
                  // decrement since data is dropped by rx_overflow
                  if (cfg.seq_cfg.en_rx_overflow) exp_rd_item.num_data--;

                  // always push the expected transaction into the queue and handle during
                  // rdata.
                  `downcast(tmp_rd_item, exp_rd_item.clone());
                  rd_pending_q.push_back(tmp_rd_item);
                  `uvm_info(`gfn, $sformatf("\nrd_pending_q.push_back"), UVM_DEBUG)
                  if (exp_rd_item.stop) begin
                    `uvm_info(`gfn, $sformatf("\nscoreboard, partial exp_rd_item\n\%s",
                        exp_rd_item.sprint()), UVM_DEBUG)
                    exp_rd_item.start = 0;
                    exp_rd_item.clear_data();
                  end
                end
              end
            end
          end
        end
        "fifo_ctrl": begin
          // these fields are WO
          bit fmtrst_val = bit'(get_field_val(ral.fifo_ctrl.fmtrst, item.a_data));
          bit rxrst_val = bit'(get_field_val(ral.fifo_ctrl.rxrst, item.a_data));
          if (rxrst_val) begin
            rd_item_fifo.flush();
            exp_rd_q.delete();
            rd_pending_q.delete();
            rd_pending_item.clear_all();
            exp_rd_item.clear_all();
          end
          if (cfg.en_cov) begin
            cov.fmt_fifo_level_cg.sample(.irq(cfg.intr_vif.pins[FmtWatermark]),
                                         .lvl(`gmv(ral.fifo_status.fmtlvl)),
                                         .rst(fmtrst_val));
          end
          if (cfg.en_cov) begin
            cov.rx_fifo_level_cg.sample(.irq(cfg.intr_vif.pins[RxWatermark]),
                                        .lvl(`gmv(ral.fifo_status.rxlvl)),
                                        .rst(rxrst_val));
          end
        end
        "intr_test": begin
          bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
          intr_exp |= item.a_data;
          if (cfg.en_cov) begin
            i2c_intr_e intr;
            foreach (intr_exp[i]) begin
              intr = i2c_intr_e'(i); // cast to enum to get interrupt name
              cov.intr_test_cg.sample(intr, item.a_data[i], intr_en[i], intr_exp[i]);
            end
          end
        end
        "txdata": begin
          if (read_rnd_data) begin
            mirrored_txdata.push_back(item.a_data[7:0]);
          end
        end
      endcase
      // get full write transaction
      if (!cfg.under_reset && host_init && sb_exp_wr_item.start && sb_exp_wr_item.stop) begin
        exp_wr_q.push_back(sb_exp_wr_item);
        num_exp_tran++;
        `uvm_info(`gfn, $sformatf("\nscoreboard, push to queue, exp_wr_item\n\%s",
            sb_exp_wr_item.sprint()), UVM_DEBUG)
      end
    end // end of write address phase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      case (csr.get_name())
        "rdata": begin
          do_read_check = 1'b0;
          if (host_init) begin
            // If read data count is 0, it means the transaction has not yet started.
            // If read data count is non-zero and equals the expected number of data while the stop
            // bit is not set, it means a chained read has been issued and we need to update the
            // expected transaction.
            if (rdata_cnt == 0 ||
                rdata_cnt == rd_pending_item.num_data && !rd_pending_item.stop) begin
              // for on-the-fly reset, immediately finish task to avoid blocking
              wait(rd_pending_q.size() > 0 || cfg.under_reset);
              if (cfg.under_reset) return;
              temp_item = rd_pending_q.pop_front();

              if (rdata_cnt == 0) begin
                // if rdata_cnt is 0, use transaction directly since it is the first
                rd_pending_item = temp_item;
              end else begin
                // if rdata_cnt is non_zero, then we are part of chain read. Update the
                // expected number of bytes and stop bit as required.
                rd_pending_item.num_data = temp_item.num_data;
                rd_pending_item.stop = temp_item.stop;
              end
            end
            rd_pending_item.data_q.push_back(item.d_data);
            rdata_cnt++;
            `uvm_info(`gfn, $sformatf("\nscoreboard, rd_pending_item\n\%s",
                rd_pending_item.sprint()), UVM_DEBUG)
            // get complete read transactions
            if (rdata_cnt == rd_pending_item.num_data && rd_pending_item.stop) begin
              `downcast(sb_exp_rd_item, rd_pending_item.clone());
              if (!cfg.under_reset) exp_rd_q.push_back(sb_exp_rd_item);
              num_exp_tran++;
              `uvm_info(`gfn, $sformatf("\nscoreboard, push to queue, exp_rd_item\n\%s",
                  sb_exp_rd_item.sprint()), UVM_DEBUG)
              rdata_cnt = 0;
            end
          end
        end
        "intr_state": begin
          i2c_intr_e     intr;
          bit [TL_DW-1:0] intr_en = item.d_data;
          do_read_check = 1'b0;
          foreach (intr_exp[i]) begin
            intr = i2c_intr_e'(i); // cast to enum to get interrupt name
            if (cfg.en_cov) begin
              cov.intr_cg.sample(intr, intr_en[intr], intr_exp[intr]);
              cov.intr_pins_cg.sample(intr, cfg.intr_vif.pins[intr]);
            end
          end
        end
        "status": begin
          // check in test
          do_read_check = 1'b0;
        end
        "fifo_status": begin
          // check in test
          do_read_check = 1'b0;
        end
        "acqdata": begin
          i2c_item obs;
          `uvm_create_obj(i2c_item, obs);
          obs = acq2item(item.d_data);
          obs.tran_id = cfg.rcvd_acq_cnt++;
          target_mode_wr_obs_port.write(obs);
          do_read_check = 1'b0;
        end
        default: begin
          // check in test
          do_read_check = 1'b0;
        end
      endcase

      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
            $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end // end of read data phase
  endtask : process_tl_access

  task compare_trans(bus_op_e dir = BusOpWrite);
    i2c_item   exp_trn;
    i2c_item   dut_trn;
    int        lastidx;
    forever begin
      if (dir == BusOpWrite) begin
        wr_item_fifo.get(dut_trn);
        wait(exp_wr_q.size() > 0);
        lastidx = dut_trn.data_q.size();
        cfg.lastbyte = dut_trn.data_q[lastidx - 1];
        exp_trn = exp_wr_q.pop_front();
      end else begin  // BusOpRead
        rd_item_fifo.get(dut_trn);
        wait(exp_rd_q.size() > 0);
        exp_trn = exp_rd_q.pop_front();
      end
      // when rx_fifo is overflow, drop the last byte from dut_trn
      if (cfg.seq_cfg.en_rx_overflow && dut_trn.bus_op == BusOpRead) begin
        void'(dut_trn.data_q.pop_back());
        dut_trn.num_data--;
      end
      if (!dut_trn.compare(exp_trn)) begin
        if (!check_overflow_data_fmt_fifo(exp_trn, dut_trn)) begin  // see description below
          `uvm_error(`gfn, $sformatf("\ndirection %s item mismatch!\n--> EXP:\n%0s\--> DUT:\n%0s",
              (dir == BusOpWrite) ? "WRITE" : "READ", exp_trn.sprint(), dut_trn.sprint()))
        end
      end else begin
        `uvm_info(`gfn, $sformatf("\ndirection %s item match!\n--> EXP:\n%0s\--> DUT:\n%0s",
            (dir == BusOpWrite) ? "WRITE" : "READ", exp_trn.sprint(), dut_trn.sprint()), UVM_MEDIUM)
      end
    end
  endtask : compare_trans

  // this function check overflowed data occured in fmt_fifo does not exist
  // in write transactions sent over busses
  function bit check_overflow_data_fmt_fifo(i2c_item exp_trn, i2c_item dut_trn);
    if (exp_trn.fmt_ovf_data_q.size() > 0) begin
      bit [7:0] unique_q[$] = dut_trn.data_q.find with
                              ( item inside {exp_trn.fmt_ovf_data_q} );
      return (unique_q.size() == 0);
    end
  endfunction : check_overflow_data_fmt_fifo

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
    rd_item_fifo.flush();
    wr_item_fifo.flush();
    exp_rd_q.delete();
    exp_wr_q.delete();
    rd_pending_q.delete();
    rd_pending_item.clear_all();
    exp_rd_item.clear_all();
    exp_wr_item.clear_all();
    host_init    = 1'b0;
    tran_id      = 0;
    rdata_cnt    = 0;
    num_exp_tran = 0;
    `uvm_info(`gfn, "\n>>> reset scoreboard", UVM_DEBUG)
    `DV_EOT_PRINT_Q_CONTENTS(i2c_item, exp_wr_q)
    `DV_EOT_PRINT_Q_CONTENTS(i2c_item, exp_rd_q)
    `DV_EOT_PRINT_Q_CONTENTS(i2c_item, rd_pending_q)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(i2c_item, rd_item_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(i2c_item, wr_item_fifo)
  endfunction : reset

  function void report_phase(uvm_phase phase);
    string str;

    super.report_phase(phase);
    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_DEBUG)
    if (cfg.en_scb) begin
      str = {$sformatf("\n*** SCOREBOARD CHECK\n")};
      str = {str, $sformatf("    - total checked trans   %0d\n", num_exp_tran)};
      `uvm_info(`gfn, $sformatf("%s", str), UVM_DEBUG)
    end
  endfunction : report_phase

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    `DV_EOT_PRINT_Q_CONTENTS(i2c_item, exp_wr_q)
    `DV_EOT_PRINT_Q_CONTENTS(i2c_item, exp_rd_q)
    `DV_EOT_PRINT_Q_CONTENTS(i2c_item, rd_pending_q)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(i2c_item, rd_item_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(i2c_item, wr_item_fifo)
  endfunction

  // Compare start, stop and wdata only
  function void target_txn_comp(i2c_item obs, i2c_item exp, string str);
    `uvm_info(`gfn, $sformatf("comp:target obs_%s_txn %0d\n%s", str, obs.tran_id, obs.sprint()),
              UVM_MEDIUM)

    `DV_CHECK_EQ(obs.tran_id, exp.tran_id)
    `DV_CHECK_EQ(obs.start, exp.start)
    `DV_CHECK_EQ(obs.stop, exp.stop)
    if (obs.stop == 0 && obs.rstart == 0) begin
      `DV_CHECK_EQ(obs.wdata, exp.wdata)
    end
  endfunction // target_txn_comp

  function void target_rd_comp(i2c_item obs, i2c_item exp);
    `uvm_info(`gfn, $sformatf("comp:target obs_rd %0d\n%s", obs.tran_id, obs.convert2string()),
              UVM_MEDIUM)
    `DV_CHECK_EQ(obs.tran_id, exp.tran_id)
    `DV_CHECK_EQ(obs.num_data, exp.num_data)
    `DV_CHECK_EQ(obs.data_q.size(), exp.data_q.size())

    foreach (exp.data_q[i]) begin
      `DV_CHECK_EQ(obs.data_q[i], exp.data_q[i])
    end
  endfunction // target_rd_comp
endclass : i2c_scoreboard
