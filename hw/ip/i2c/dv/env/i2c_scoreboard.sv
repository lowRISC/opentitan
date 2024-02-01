// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_scoreboard extends cip_base_scoreboard #(
    .CFG_T(i2c_env_cfg),
    .RAL_T(i2c_reg_block),
    .COV_T(i2c_env_cov)
  );
  `uvm_component_utils(i2c_scoreboard)

  virtual i2c_if  i2c_vif;

  // Local seq_items used to construct larger transactions.
  // Construct txn_items by updating the local items as different
  // events occur, then push the item into a queue for checking after the
  // end of the transaction has been detected.
  local i2c_item  exp_rd_item;
  local i2c_item  exp_wr_item;
  local i2c_item  obs_wr_item;
  local i2c_item  obs_rd_item;
  local i2c_item  rd_pending_item; // Store partially-complete state of read txn in host-mode
  local uint      rd_wait;
  local bit       host_init = 1'b0;
  local uint      rdata_cnt = 0; // Count data-bytes read from a target in host-mode
  local uint      tran_id = 0;
  local uint      num_exp_tran = 0;

  // DUT in HOST mode
  ///////////////////
  // These queues hold items representing full read or write transactions,
  // assembled by monitoring the TL-interface to the HWIP block.
  // As there is no model required to predict the transaction that should be
  // recorded by the monitors (it is a pure comms system, the output data
  // should exactly equal the input data), these queues become the source of
  // expected 'exp_trn' items in the 'compare_trans' checker method.
  local i2c_item  exp_wr_q[$];
  local i2c_item  exp_rd_q[$];
  local i2c_item  rd_pending_q[$]; // Helper-queue : hold partial read transactions (data-phase)

  // TLM fifos hold the transactions sent by monitor
  // These become the source of measured 'dut_trn' items in the 'compare_trans'
  // checker method.
  uvm_tlm_analysis_fifo #(i2c_item) rd_item_fifo;
  uvm_tlm_analysis_fifo #(i2c_item) wr_item_fifo;
  ///////////////////

  // DUT in TARGET/DEVICE mode
  ///////////////////
  // Captures an item-per-byte read from 'ACQDATA' register
  uvm_analysis_port #(i2c_item) target_mode_wr_obs_port;
  // Target mode seq_item queues (wr/rd transactions)
  uvm_tlm_analysis_fifo #(i2c_item) target_mode_wr_exp_fifo;
  uvm_tlm_analysis_fifo #(i2c_item) target_mode_wr_obs_fifo;
  uvm_tlm_analysis_fifo #(i2c_item) target_mode_rd_exp_fifo;
  uvm_tlm_analysis_fifo #(i2c_item) target_mode_rd_obs_fifo;
  ///////////////////

  // interrupt bit vector
  local bit [NumI2cIntr-1:0] intr_exp;

  int                        num_obs_rd;
  int                        obs_wr_id = 0;
  bit                        skip_acq_comp = 0; // used only for fifo_reset test

  // In Target-mode, read data is created by i2c_base_seq::fetch_txn().
  // With a random tx fifo flush event, this makes it difficult to check read path integrity.
  // By setting 'read_rnd_data = 1', expected read data is collected right at the input of tx fifo
  // and at the tx fifo reset event, expected read data also get flushed.
  bit                        read_rnd_data = 0;
  bit [7:0]                  mirrored_txdata[$];

  // skip segment comparison
  bit                        skip_target_txn_comp = 0;
  bit                        skip_target_rd_comp = 0;

  // Variable to sample fmt fifo data
  i2c_item                   fmt_fifo_data_q[$];
  i2c_item                   fmt_fifo_data;
  // Host mode stretch timeout control enable
  bit                        host_timeout_ctrl_en;

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
    `uvm_create_obj(i2c_item, fmt_fifo_data)
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    target_mode_wr_obs_port.connect(target_mode_wr_obs_fifo.analysis_export);
    cfg.scb_h = this;
  endfunction

  task run_phase(uvm_phase phase);
    string str;
    super.run_phase(phase);
    sample_scl_stretch_cg();
    //-----------------------------------------------
    // Checks for I2C DUT in TARGET/DEVICE mode
    // - (agent in HOST mode)
    //-----------------------------------------------
    if (cfg.m_i2c_agent_cfg.if_mode == Host) begin
      fork
        // Compare seq_items for write transactions
        // Currently, items for this check are captures byte-by-byte at the ACQFIFO reg
        // Hence, we check only compare start, stop and wdata fields of the item.
        forever begin
          fork begin
            fork
              begin
                target_mode_wr_obs_fifo.get(obs_wr_item);
                if (!skip_target_txn_comp) begin
                  if (cfg.en_cov) begin
                    cov.sample_i2c_b2b_cg(obs_wr_item.addr,
                                          ral.ctrl.enablehost.get_mirrored_value());
                  end
                  obs_wr_item.tran_id = obs_wr_id++;
                  target_mode_wr_exp_fifo.get(exp_wr_item);
                  str = (exp_wr_item.start) ? "addr" : (exp_wr_item.stop) ? "stop" : "wr";
                  `uvm_info(`gfn, $sformatf("exp_%s_txn %0d\n %s", str,
                            exp_wr_item.tran_id, exp_wr_item.sprint()), UVM_MEDIUM)
                  target_txn_comp(obs_wr_item, exp_wr_item, str);
                end
              end
              begin
                wait(skip_acq_comp);
                cfg.clk_rst_vif.wait_clks(1);
              end
            join_any
            disable fork;
          end join
        end
        // Compare seq_items for read transactions
        forever begin
          target_mode_rd_obs_fifo.get(obs_rd_item);
          if (!skip_target_rd_comp) begin
            if (cfg.en_cov) begin
              cov.sample_i2c_b2b_cg(obs_rd_item.addr, ral.ctrl.enablehost.get_mirrored_value());
            end
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
        end
      join_none
    //-----------------------------------------------
    // Checks for I2C DUT in HOST mode
    // - (agent in TARGET/DEVICE mode)
    //-----------------------------------------------
    end else if (cfg.m_i2c_agent_cfg.if_mode == Device) begin
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

  // Task to sample the i2c_scl_stretch_cg based on the interrupts and FIFO status
  task sample_scl_stretch_cg();
    if (cfg.en_cov) begin
      fork
        forever begin
          uint acqlvl, txlvl;
          bit timeout_ctrl_en;
          fork
            wait(cfg.intr_vif.pins[StretchTimeout]);
            wait(cfg.intr_vif.pins[TxStretch]);
            wait(cfg.intr_vif.pins[AcqFull]);
          join_any
          csr_rd(.ptr(ral.target_fifo_status.acqlvl), .value(acqlvl), .backdoor(UVM_BACKDOOR));
          csr_rd(.ptr(ral.target_fifo_status.txlvl), .value(txlvl), .backdoor(UVM_BACKDOOR));
          cov.scl_stretch_cg.sample(
            .host_mode(host_init),
            .intr_stretch_timeout(cfg.intr_vif.pins[StretchTimeout]),
            .host_timeout_ctrl_en(host_timeout_ctrl_en),
            .intr_tx_stretch(cfg.intr_vif.pins[TxStretch]),
            .intr_acq_full(cfg.intr_vif.pins[AcqFull]),
            .acq_fifo_size(acqlvl),
            .tx_fifo_size(txlvl)
            );
        cfg.clk_rst_vif.wait_clks(1);
        end
      join_none
    end
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg   csr;
    i2c_item  sb_exp_wr_item; // tmpvar : Push into 'exp_wr_q' once a full txn is assembled
    i2c_item  sb_exp_rd_item; // tmpvar : Push into 'exp_rd_q' once a full txn is assembled
    i2c_item  temp_item;

    // After reads, if do_read_check is set, compare the mirrored_value against item.d_data
    bit do_read_check = 1'b1;

    bit write = item.is_write();
    bit addr_phase_read = (!write && channel == AddrChannel);
    bit addr_phase_write = (write && channel == AddrChannel);
    bit data_phase_read = (!write && channel == DataChannel);
    bit data_phase_write = (write && channel == DataChannel);

    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("\naccess unexpected addr 0x%0h", csr_addr))
    end

    // The access is to a valid CSR, now process it.
    // writes -> update local variable and fifo at A-channel access
    // reads  -> update predication at address phase and compare at D-channel access

    sb_exp_wr_item = new();
    if (addr_phase_write) begin
      // incoming access is a write to a valid csr, so make updates right away
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));

      case (csr.get_name())
        "ctrl": begin
          host_init = ral.ctrl.enablehost.get_mirrored_value();
          if (cfg.en_cov) begin
            cov.openting_mode_cg.sample(.ip_mode(host_init),
                                        .tb_mode(!host_init),
                                        .scl_frequency(cfg.scl_frequency));
          end
        end
        "timeout_ctrl": begin
          host_timeout_ctrl_en = ral.timeout_ctrl.en.get_mirrored_value();
        end

        "target_id": begin
           cfg.m_i2c_agent_cfg.target_addr0 = get_field_val(ral.target_id.address0, item.a_data);
           cfg.m_i2c_agent_cfg.target_addr1 = get_field_val(ral.target_id.address1, item.a_data);
        end

        "fdata": begin
          bit [7:0] fbyte;
          bit start, stop, read, rcont, nakok;
          if (!cfg.under_reset && host_init) begin
            fbyte = get_field_val(ral.fdata.fbyte, item.a_data);
            start = bit'(get_field_val(ral.fdata.start, item.a_data));
            stop  = bit'(get_field_val(ral.fdata.stop, item.a_data));
            read  = bit'(get_field_val(ral.fdata.readb, item.a_data));
            rcont = bit'(get_field_val(ral.fdata.rcont, item.a_data));
            nakok = bit'(get_field_val(ral.fdata.nakok, item.a_data));
            if (cfg.en_cov) begin
              i2c_item fmt_data;
              fmt_fifo_data.fbyte = fbyte;
              fmt_fifo_data.start = start;
              fmt_fifo_data.stop  = stop;
              fmt_fifo_data.read  = read;
              fmt_fifo_data.rcont = rcont;
              fmt_fifo_data.nakok = nakok;
              `downcast(fmt_data, fmt_fifo_data.clone());
              fmt_fifo_data_q.push_back(fmt_data); // push data to fmt_fifo_data_q
            end
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
                exp_wr_item.data_q.push_back(fbyte);
                exp_wr_item.num_data++;
                exp_wr_item.stop = stop;
                if (exp_wr_item.stop) begin
                  // get a complete write
                  `downcast(sb_exp_wr_item, exp_wr_item.clone());
                  exp_wr_item.clear_all();
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
          bit acqrst_val = bit'(get_field_val(ral.fifo_ctrl.acqrst, item.a_data));
          bit txrst_val = bit'(get_field_val(ral.fifo_ctrl.txrst, item.a_data));
          if (rxrst_val) begin
            rd_item_fifo.flush();
            exp_rd_q.delete();
            rd_pending_q.delete();
            rd_pending_item.clear_all();
            exp_rd_item.clear_all();
          end
          if (cfg.en_cov) begin
            if (fmtrst_val) begin
              fmt_fifo_data_q.delete();
            end
            cov.fmt_fifo_level_cg.sample(.irq(cfg.intr_vif.pins[FmtThreshold]),
                                         .fifolvl(`gmv(ral.host_fifo_status.fmtlvl)),
                                         .rst(fmtrst_val));
            cov.rx_fifo_level_cg.sample(.irq(cfg.intr_vif.pins[RxThreshold]),
                                        .fifolvl(`gmv(ral.host_fifo_status.rxlvl)),
                                        .rst(rxrst_val));
            cov.fifo_reset_cg.sample(.fmtrst(fmtrst_val),
                                     .rxrst (rxrst_val),
                                     .acqrst(acqrst_val),
                                     .txrst (txrst_val),
                                     .fmt_threshold(cfg.intr_vif.pins[FmtThreshold]),
                                     .rx_threshold (cfg.intr_vif.pins[RxThreshold]),
                                     .acq_threshold(cfg.intr_vif.pins[AcqThreshold]),
                                     .rx_overflow  (cfg.intr_vif.pins[RxOverflow]),
                                     .acq_overflow (cfg.intr_vif.pins[AcqFull]),
                                     .tx_threshold (cfg.intr_vif.pins[TxThreshold]));
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
          if (cfg.en_cov) begin
            cov.interrupts_cg.sample(.intr_state(ral.intr_state.get_mirrored_value()),
                                     .intr_enable(ral.intr_enable.get_mirrored_value()),
                                     .intr_test(item.a_data));
          end
        end

        "intr_enable" : begin
          if (cfg.en_cov) begin
            cov.interrupts_cg.sample(.intr_state(ral.intr_state.get_mirrored_value()),
                                     .intr_enable(item.a_data),
                                     .intr_test(ral.intr_test.get_mirrored_value()));
          end
        end

        "txdata": begin
          if (read_rnd_data) begin
            mirrored_txdata.push_back(item.a_data[7:0]);
          end
        end
        "timing0": begin
          if (cfg.en_cov) begin
            cov.thigh_cg.sample(`gmv(ral.timing0.thigh));
            cov.tlow_cg.sample(`gmv(ral.timing0.thigh));
          end
        end
        "timing1": begin
          if (cfg.en_cov) begin
            cov.t_r_cg.sample(`gmv(ral.timing1.t_r));
            cov.t_f_cg.sample(`gmv(ral.timing1.t_f));
          end
        end
        "timing2": begin
          if (cfg.en_cov) begin
            cov.tsu_sta_cg.sample(`gmv(ral.timing2.tsu_sta));
            cov.thd_sta_cg.sample(`gmv(ral.timing2.thd_sta));
          end
        end
        "timing3": begin
          if (cfg.en_cov) begin
            cov.tsu_dat_cg.sample(`gmv(ral.timing3.tsu_dat));
            cov.thd_dat_cg.sample(`gmv(ral.timing3.thd_dat));
          end
        end
        "timing4": begin
          if (cfg.en_cov) begin
            cov.t_buf_cg.sample(`gmv(ral.timing4.t_buf));
            cov.tsu_sto_cg.sample(`gmv(ral.timing4.tsu_sto));
          end
        end
      endcase

      if (cfg.under_reset || !host_init) return;
      // If we have completed a transaction (detected both start and stop)
      //   - Push a completed txn item to the queue
      if (sb_exp_wr_item.start &&
          sb_exp_wr_item.stop) begin
        exp_wr_q.push_back(sb_exp_wr_item); num_exp_tran++;
        `uvm_info(`gfn,
          $sformatf("\nscoreboard, push to queue, exp_wr_item\n\%s", sb_exp_wr_item.sprint()),
          UVM_DEBUG)
      end
    end // addr_phase_write

    sb_exp_rd_item = new();
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
            `uvm_info(`gfn,
              $sformatf("\nscoreboard, rd_pending_item\n\%s", rd_pending_item.sprint()),
              UVM_DEBUG)
            // Push completed read transactions into the 'exp_rd_q'
            if (rd_pending_item.num_data == rdata_cnt &&
                rd_pending_item.stop) begin
              `downcast(sb_exp_rd_item, rd_pending_item.clone());
              if (!cfg.under_reset) exp_rd_q.push_back(sb_exp_rd_item);
              num_exp_tran++;
              `uvm_info(`gfn,
                $sformatf("\nscoreboard, push to queue, exp_rd_item\n\%s", sb_exp_rd_item.sprint()),
                UVM_DEBUG)
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
          if (cfg.en_cov) begin
            cov.interrupts_cg.sample(.intr_state(item.a_data),
                                     .intr_enable(ral.intr_enable.get_mirrored_value()),
                                     .intr_test(ral.intr_test.get_mirrored_value()));
          end
        end
        "intr_test" : begin
          if (cfg.en_cov) begin
            cov.interrupts_cg.sample(.intr_state(ral.intr_state.get_mirrored_value()),
                                     .intr_enable(ral.intr_enable.get_mirrored_value()),
                                     .intr_test(item.a_data));
          end
        end
        "intr_enable" : begin
          if (cfg.en_cov) begin
            cov.interrupts_cg.sample(.intr_state(ral.intr_state.get_mirrored_value()),
                                     .intr_enable(item.a_data),
                                     .intr_test(ral.intr_test.get_mirrored_value()));
          end
        end

        "status": begin
          do_read_check = 1'b0;
          if (cfg.en_cov) begin
            cov.status_cg.sample(
              .fmtfull   (`gmv(ral.status.fmtfull)),
              .rxfull    (`gmv(ral.status.rxfull)),
              .fmtempty  (`gmv(ral.status.fmtempty)),
              .hostidle  (`gmv(ral.status.hostidle)),
              .targetidle(`gmv(ral.status.targetidle)),
              .rxempty   (`gmv(ral.status.rxempty)),
              .txfull    (`gmv(ral.status.txfull)),
              .acqfull   (`gmv(ral.status.acqfull)),
              .txempty   (`gmv(ral.status.txempty)),
              .acqempty  (`gmv(ral.status.acqempty))
            );
          end
        end

        "host_fifo_status": do_read_check = 1'b0;
        "target_fifo_status": do_read_check = 1'b0;

        "acqdata": begin
          i2c_item obs;
          `uvm_create_obj(i2c_item, obs);
          obs = acq2item(item.d_data);
          obs.tran_id = cfg.rcvd_acq_cnt++;
          target_mode_wr_obs_port.write(obs);
          do_read_check = 1'b0;
          if (cfg.en_cov) begin
            cov.acq_fifo_cg.sample(.abyte(item.d_data[7:1]),
                                   .rw_ack_nack(item.d_data[0]),
                                   .signal(item.d_data[9:8]));
          end
        end

        "ovrd": begin
          do_read_check = 1'b0;
          if (cfg.en_cov) begin
            cov.scl_sda_override_cg.sample(
              .txovrden(`gmv(ral.ovrd.txovrden)),
              .sclval(`gmv(ral.ovrd.sclval)),
              .sdaval(`gmv(ral.ovrd.sdaval))
            );
          end
        end

        "host_fifo_config":   do_read_check = 1'b0;
        "target_fifo_config": do_read_check = 1'b0;

        default: do_read_check = 1'b0;
      endcase

      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
            $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end // data_phase_read
  endtask : process_tl_access

  // Task to sample FMT FIFO data along with ACK/NACK status
  // For Read transactions, one entry of FMT FIFO data is sampled
  //     since read data is captured in RXDAT FIFO
  // For Write transactions, multiple entries of FMT FIFO data are sampled
  //     since write data is encoded in to multiple fbyte values
  task sample_fmt_fifo_data(ref i2c_item dut_trn);
    if (cfg.en_cov) begin
      i2c_item fmt_data;
      `uvm_info(`gfn, $sformatf("exp_txn.addr_ack = %0b", dut_trn.addr_ack), UVM_DEBUG)
      fmt_data = fmt_fifo_data_q.pop_front();
      `uvm_info(`gfn, dut_trn.sprint(), UVM_DEBUG)
      `uvm_info(`gfn, fmt_data.sprint(), UVM_DEBUG)
      cov.fmt_fifo_cg.sample(
        .fbyte(fmt_data.fbyte),
        .start(fmt_data.start),
        .stop(fmt_data.stop),
        .read(fmt_data.read),
        .rcont(fmt_data.rcont),
        .nakok(fmt_data.nakok),
        .ack_int_recv(dut_trn.read ? dut_trn.ack : dut_trn.addr_ack)
        );
        `uvm_info(`gfn,
          $sformatf("fmt_data.size = %0d ; dut_trn.size = %0d",
            fmt_fifo_data_q.size(),
            dut_trn.data_q.size()),
          UVM_MEDIUM)
      if (dut_trn.bus_op != BusOpRead) begin
        foreach(dut_trn.data_q[i]) begin
          fmt_data = fmt_fifo_data_q.pop_front();
          cov.fmt_fifo_cg.sample(
            .start(fmt_data.start),
            .stop(fmt_data.stop),
            .read(fmt_data.read),
            .rcont(fmt_data.rcont),
            .nakok(fmt_data.nakok),
            .fbyte(fmt_data.fbyte),
            .ack_int_recv(fmt_data.data_ack_q[i])
          );
        end
      end
    end

  endtask

  task compare_trans(bus_op_e dir = BusOpWrite);
    i2c_item   exp_trn;
    i2c_item   dut_trn;
    int        lastidx;
    forever begin
      if (dir == BusOpWrite) begin
        wr_item_fifo.get(dut_trn);
        if (cfg.en_cov) begin
          cov.sample_i2c_b2b_cg(dut_trn.addr, ral.ctrl.enablehost.get_mirrored_value());
        end
        wait(exp_wr_q.size() > 0);
        lastidx = dut_trn.data_q.size();
        cfg.lastbyte = dut_trn.data_q[lastidx - 1];
        exp_trn = exp_wr_q.pop_front();
      end else begin  // BusOpRead
        rd_item_fifo.get(dut_trn);
        if (cfg.en_cov) begin
          cov.sample_i2c_b2b_cg(dut_trn.addr, ral.ctrl.enablehost.get_mirrored_value());
        end
        wait(exp_rd_q.size() > 0);
        exp_trn = exp_rd_q.pop_front();
      end
      sample_fmt_fifo_data(dut_trn);
      if (!cfg.en_scb) begin // Skip comparison
        `uvm_info(`gfn, "Scoreboard disabled", UVM_LOW)
        continue;
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
    num_obs_rd = 0;
    obs_wr_id = 0;
    target_mode_wr_exp_fifo.flush();
    target_mode_wr_obs_fifo.flush();
    target_mode_rd_exp_fifo.flush();
    target_mode_rd_obs_fifo.flush();
    mirrored_txdata.delete();
    fmt_fifo_data_q.delete();
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
