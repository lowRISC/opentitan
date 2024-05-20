// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_scoreboard extends cip_base_scoreboard #(
    .CFG_T(i2c_env_cfg),
    .RAL_T(i2c_reg_block),
    .COV_T(i2c_env_cov)
  );
  `uvm_component_utils(i2c_scoreboard)

  i2c_reference_model model; // Handle to the env's reference model

  ////////////////////
  // DUT-Controller //
  ////////////////////

  uvm_tlm_analysis_fifo #(i2c_item) controller_mode_wr_exp_fifo; // Input -> RefModel
  uvm_tlm_analysis_fifo #(i2c_item) controller_mode_wr_obs_fifo; // Input -> Monitor (wr_item_port)
  uvm_tlm_analysis_fifo #(i2c_item) controller_mode_rd_exp_fifo; // Input -> RefModel
  uvm_tlm_analysis_fifo #(i2c_item) controller_mode_rd_obs_fifo; // Input -> Monitor (rd_item_port)

  ////////////////
  // DUT-Target //
  ////////////////

  uvm_tlm_analysis_fifo #(i2c_item) target_mode_wr_exp_fifo; // Input -> StimVseqs (via. RefModel)
  uvm_tlm_analysis_fifo #(i2c_item) target_mode_wr_obs_fifo; // Input -> ACQFIFO rd (via. RefModel)
  uvm_tlm_analysis_fifo #(i2c_item) target_mode_rd_exp_fifo; // Input -> StimVseqs (via. RefModel)
  uvm_tlm_analysis_fifo #(i2c_item) target_mode_rd_obs_fifo; // Input -> Monitor 'analysis_port'

  // interrupt bit vector
  local bit [NumI2cIntr-1:0] intr_exp;

  // Counters for DUT-Target transactions
  uint dut_target_exp_read_transfer_id = 0;
  uint dut_target_obs_read_transfer_id = 0;
  uint dut_target_exp_write_transfer_id = 0;
  uint dut_target_obs_write_transfer_id = 0;
  // Counters for DUT-Controller transactions
  uint dut_controller_transfer_id = 0;

  // These events reset the comparison routines for DUT-Target transactions.
  uvm_event reset_dut_target_wr_compare;
  uvm_event reset_dut_target_rd_compare;

  // (Coverage only) Queue for fmtfifo data to be sampled
  i2c_item  fmt_fifo_data_q[$];

  `uvm_component_new

  ///////////////////
  // CLASS METHODS //
  ///////////////////
  //
  // {build,connect,run,report,check}_phase()
  //
  // process_tl_access()
  //   sample_write_coverage()
  //   sample_read_coverage()
  //
  // compare_target_write_trans()
  // compare_target_read_trans()
  // compare_controller_trans(bus_op_e dir) // READ+WRITE
  // target_wr_comp()/target_rd_comp()
  //
  // collect_scl_stretch_cg()
  // sample_fmt_fifo_data()
  //
  //////////////////////////////////////

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    controller_mode_wr_obs_fifo = new("controller_mode_wr_obs_fifo", this);
    controller_mode_wr_exp_fifo = new("controller_mode_wr_exp_fifo", this);
    controller_mode_rd_obs_fifo = new("controller_mode_rd_obs_fifo", this);
    controller_mode_rd_exp_fifo = new("controller_mode_rd_exp_fifo", this);
    target_mode_wr_exp_fifo = new("target_mode_wr_exp_fifo", this);
    target_mode_wr_obs_fifo = new("target_mode_wr_obs_fifo", this);
    target_mode_rd_exp_fifo = new("target_mode_rd_exp_fifo", this);
    target_mode_rd_obs_fifo = new("target_mode_rd_obs_fifo", this);
    reset_dut_target_rd_compare = new("reset_dut_target_rd_compare");
    reset_dut_target_wr_compare = new("reset_dut_target_wr_compare");
  endfunction: build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    cfg.scoreboard = this;
  endfunction: connect_phase

  task run_phase(uvm_phase phase);
    super.run_phase(phase);

    if (cfg.en_cov) collect_scl_stretch_cg();

    case (cfg.m_i2c_agent_cfg.if_mode)
      //-----------------------------------------------
      // DUT:Agent == TARGET:CONTROLLER
      //-----------------------------------------------
      Host: begin
        // Spawn two threads which await and check read and write
        // transactions independently.
        fork
          // Compare write transactions
          forever begin
            fork begin: iso_fork
              // The event 'reset_dut_target_wr_compare' can be used to
              // abandon the current comparison routine, and force it to
              // start again at the top. This is useful for fault-injection.
              fork
                compare_target_write_trans();
                begin
                  reset_dut_target_wr_compare.wait_trigger();
                  `uvm_info(`gfn, "dut_target_wr_compare routine is reset now.", UVM_MEDIUM)
                end
              join_any
              disable fork;
            end : iso_fork join
          end
          // Compare seq_items for read transactions
          forever begin
            fork begin: iso_fork2
              // The event 'reset_dut_target_rd_compare' can be used to
              // abandon the current comparison routine, and force it to
              // start again at the top. This is useful for fault-injection.
              fork
                compare_target_read_trans();
                begin
                  reset_dut_target_rd_compare.wait_trigger();
                  `uvm_info(`gfn, "dut_target_rd_compare routine is reset now.", UVM_MEDIUM)
                end
              join_any
              disable fork;
            end : iso_fork2 join
          end
        join_none
      end
      //-----------------------------------------------
      // DUT:Agent == CONTROLLER:TARGET
      //-----------------------------------------------
      Device: begin
        // Spawn two parallel threads to check read and write
        // transactions respectively.
        forever begin
          `DV_SPINWAIT_EXIT(
            // WAIT_
            wait(cfg.clk_rst_vif.rst_n === 1'b1)
            fork
              forever compare_controller_trans(BusOpWrite);
              forever compare_controller_trans(BusOpRead);
            join,
            // EXIT_
            @(negedge cfg.clk_rst_vif.rst_n),
          )
        end
      end
      default:;
    endcase
  endtask: run_phase

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    dv_base_reg_block i2c_ral = cfg.ral_models[ral_name];
    uvm_reg_addr_t csr_addr = i2c_ral.get_word_aligned_addr(item.a_addr);
    uvm_reg csr;

    bit write = item.is_write();
    bit tl_get           = (!write && channel == AddrChannel);
    bit tl_putdata       =  (write && channel == AddrChannel); // write
    bit tl_accessackdata = (!write && channel == DataChannel); // read
    bit tl_accessack     =  (write && channel == DataChannel);

    // If access was not addressed to a valid csr, raise a fatal error
    if (!(csr_addr inside {i2c_ral.csr_addrs})) begin
      `uvm_fatal(`gfn, $sformatf("An unexpected addr 0x%8h was accessed.", csr_addr))
    end

    // The access was to a valid csr, so get the corresponding RAL csr handle
    csr = i2c_ral.default_map.get_reg_by_offset(csr_addr);
    `DV_CHECK_NE_FATAL(csr, null)

    // Update the reference model based on the TL-UL access
    // - This also updates the RAL
    model.process_tl_access(item, channel, ral_name, csr);

    // Collect fcov based on the access
    if (tl_putdata) sample_write_coverage(item.a_data, csr);
    if (tl_accessackdata) sample_read_coverage(item.d_data, csr);
  endtask : process_tl_access


  // Sample functional coverage points based on write data to a valid CSR.
  //
  virtual task sample_write_coverage(bit [bus_params_pkg::BUS_DW-1:0] data, uvm_reg csr);

    case (csr.get_name())
      "ctrl": begin
        if (cfg.en_cov) begin
          cov.openting_mode_cg.sample(.ip_mode(`gmv(ral.ctrl.enablehost)),
                                      .tb_mode(!(`gmv(ral.ctrl.enablehost))),
                                      .scl_frequency(cfg.scl_frequency));
        end
      end

      "fdata": begin // aka. FMTFIFO

        // Only capture coverage if not in reset, and HOST/CONTROLLER mode
        // is active.
        if (!cfg.under_reset && `gmv(ral.ctrl.enablehost)) begin

          bit [7:0] fbyte = get_field_val(ral.fdata.fbyte, data);
          bit start = get_field_val(ral.fdata.start, data);
          bit stop  = get_field_val(ral.fdata.stop, data);
          bit readb = get_field_val(ral.fdata.readb, data);
          bit rcont = get_field_val(ral.fdata.rcont, data);
          bit nakok = get_field_val(ral.fdata.nakok, data);

          // Sample for coverage
          // - Data is pushed to 'fmt_fifo_data_q', which is popped off in
          //   sample_fmt_fifo_data() when both exp/obs parts of the transfer
          //   have been captured for comparison.
          if (cfg.en_cov) begin
            i2c_item fmt_fifo_data;
            `uvm_create_obj(i2c_item, fmt_fifo_data)
            fmt_fifo_data.fbyte = fbyte;
            fmt_fifo_data.start = start;
            fmt_fifo_data.stop  = stop;
            fmt_fifo_data.read  = readb;
            fmt_fifo_data.rcont = rcont;
            fmt_fifo_data.nakok = nakok;
            fmt_fifo_data_q.push_back(fmt_fifo_data);
          end

        end // (!cfg.under_reset && `gmv(ral.ctrl.enablehost))

      end

      "fifo_ctrl": begin
        // these fields are WO
        bit fmtrst_val = get_field_val(ral.fifo_ctrl.fmtrst, data);
        bit rxrst_val = get_field_val(ral.fifo_ctrl.rxrst, data);
        bit acqrst_val = get_field_val(ral.fifo_ctrl.acqrst, data);
        bit txrst_val = get_field_val(ral.fifo_ctrl.txrst, data);
        if (rxrst_val) begin
          // TODO: FLUSH FIFOS
        end
        if (cfg.en_cov) begin
          if (fmtrst_val) fmt_fifo_data_q.delete();
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
                                   .acq_overflow (cfg.intr_vif.pins[AcqStretch]),
                                   .tx_threshold (cfg.intr_vif.pins[TxThreshold]));
        end
      end

      "intr_test": begin
        bit [TL_DW-1:0] intr_en = `gmv(ral.intr_enable);
        intr_exp |= data;
        if (cfg.en_cov) begin
          i2c_intr_e intr;
          foreach (intr_exp[i]) begin
            intr = i2c_intr_e'(i); // cast to enum to get interrupt name
            cov.intr_test_cg.sample(intr, data[i], intr_en[i], intr_exp[i]);
          end
        end
        if (cfg.en_cov) begin
          cov.interrupts_cg.sample(.intr_state(`gmv(ral.intr_state)),
                                   .intr_enable(`gmv(ral.intr_enable)),
                                   .intr_test(data));
        end
      end

      "intr_enable" : begin
        if (cfg.en_cov) begin
          cov.interrupts_cg.sample(.intr_state(`gmv(ral.intr_state)),
                                   .intr_enable(data),
                                   .intr_test(`gmv(ral.intr_test)));
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

      default:;
    endcase

  endtask: sample_write_coverage


  // Sample functional coverage points based on read data from a valid CSR.
  //
  virtual task sample_read_coverage(bit [bus_params_pkg::BUS_DW-1:0] data, uvm_reg csr);

    case (csr.get_name())
      "rdata":;

      "intr_state": begin
        i2c_intr_e intr;
        bit [TL_DW-1:0] intr_en = data;
        foreach (intr_exp[i]) begin
          intr = i2c_intr_e'(i); // cast to enum to get interrupt name
          if (cfg.en_cov) begin
            cov.intr_cg.sample(intr, intr_en[intr], intr_exp[intr]);
            cov.intr_pins_cg.sample(intr, cfg.intr_vif.pins[intr]);
          end
        end
        if (cfg.en_cov) begin
          cov.interrupts_cg.sample(.intr_state(data),
                                   .intr_enable(`gmv(ral.intr_enable)),
                                   .intr_test(`gmv(ral.intr_test)));
        end
      end
      "intr_test" : begin
        if (cfg.en_cov) begin
          cov.interrupts_cg.sample(.intr_state(`gmv(ral.intr_state)),
                                   .intr_enable(`gmv(ral.intr_enable)),
                                   .intr_test(data));
        end
      end
      "intr_enable" : begin
        if (cfg.en_cov) begin
          cov.interrupts_cg.sample(.intr_state(`gmv(ral.intr_state)),
                                   .intr_enable(data),
                                   .intr_test(`gmv(ral.intr_test)));
        end
      end

      "status": begin
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

      "acqdata": begin
        if (cfg.en_cov) begin
          cov.acq_fifo_cg.sample(.abyte(data[7:1]),
                                 .rw_ack_nack(data[0]),
                                 .signal(data[9:8]));
        end
      end

      "ovrd": begin
        if (cfg.en_cov) begin
          cov.scl_sda_override_cg.sample(
            .txovrden(`gmv(ral.ovrd.txovrden)),
            .sclval(`gmv(ral.ovrd.sclval)),
            .sdaval(`gmv(ral.ovrd.sdaval))
            );
        end
      end

      default:;
    endcase

  endtask: sample_read_coverage

  // Task to sample FMT FIFO data along with ACK/NACK status
  // For Read transactions, one entry of FMT FIFO data is sampled
  //     since read data is captured in RXFIFO
  // For Write transactions, multiple entries of FMT FIFO data are sampled
  //     since write data is encoded in to multiple fbyte values
  task sample_fmt_fifo_data(ref i2c_item dut_trn);
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
    `uvm_info(`gfn, $sformatf("fmt_data.size = %0d ; dut_trn.size = %0d",
      fmt_fifo_data_q.size(), dut_trn.data_q.size()), UVM_MEDIUM)

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
  endtask

  // Task to sample the i2c_scl_stretch_cg based on the interrupts and FIFO status
  task collect_scl_stretch_cg();
    fork
      forever begin
        uint acqlvl, txlvl;
        bit timeout_ctrl_en;
        fork
          wait(cfg.intr_vif.pins[StretchTimeout]);
          wait(cfg.intr_vif.pins[TxStretch]);
          wait(cfg.intr_vif.pins[AcqStretch]);
        join_any
        csr_rd(.ptr(ral.target_fifo_status.acqlvl), .value(acqlvl), .backdoor(UVM_BACKDOOR));
        csr_rd(.ptr(ral.target_fifo_status.txlvl), .value(txlvl), .backdoor(UVM_BACKDOOR));
        cov.scl_stretch_cg.sample(
          .host_mode(`gmv(ral.ctrl.enablehost)),
          .intr_stretch_timeout(cfg.intr_vif.pins[StretchTimeout]),
          .host_timeout_ctrl_en(`gmv(ral.timeout_ctrl.en)),
          .intr_tx_stretch(cfg.intr_vif.pins[TxStretch]),
          .intr_acq_stretch(cfg.intr_vif.pins[AcqStretch]),
          .acq_fifo_size(acqlvl),
          .tx_fifo_size(txlvl)
        );
        cfg.clk_rst_vif.wait_clks(1);
      end
    join_none
  endtask: collect_scl_stretch_cg

  // Compare seq_items for write transactions
  // OBS: captured byte-by-byte upon reading the ACQFIFO
  // EXP: generated when we created the stimulus (fetch_txn())
  //
  // We only check the start, stop and wdata fields of the item.
  task compare_target_write_trans();
    i2c_item obs_wr, exp_wr;

    // Block until both items are received
    fork
      begin
        `uvm_info(`gfn, "Awaiting obs_wr item.", UVM_HIGH)
        cfg.wait_fifo_not_empty(target_mode_wr_obs_fifo);
        `uvm_info(`gfn, "obs_wr item has arrived, not yet popping from stack.", UVM_HIGH)
      end
      begin
        `uvm_info(`gfn, "Awaiting exp_wr item.", UVM_HIGH)
        cfg.wait_fifo_not_empty(target_mode_wr_exp_fifo);
        `uvm_info(`gfn, "exp_wr item has arrived, not yet popping from stack.", UVM_HIGH)
      end
    join
    target_mode_wr_obs_fifo.get(obs_wr);
    obs_wr.tran_id = dut_target_obs_write_transfer_id++;
    `uvm_info(`gfn, $sformatf("Popped obs_wr item %0d.", obs_wr.tran_id), UVM_HIGH)
    target_mode_wr_exp_fifo.get(exp_wr);
    exp_wr.tran_id = dut_target_exp_write_transfer_id++;
    `uvm_info(`gfn, $sformatf("Popped exp_wr item %0d.", exp_wr.tran_id), UVM_HIGH)

    // Sample the covergroup before doing the comparison.
    if (cfg.en_cov) begin
      cov.sample_i2c_b2b_cg(obs_wr.addr, `gmv(ral.ctrl.enablehost));
    end

    target_wr_comp(obs_wr, exp_wr);
  endtask: compare_target_write_trans

  // Compare seq_items for read transactions
  // - OBS: Captured by the monitor
  // - EXP: Created when we generated the stimulus (fetch_txn())
  task compare_target_read_trans();
    i2c_item obs_rd, exp_rd;

    // Block until both items are received
    fork
      begin
        `uvm_info(`gfn, "Awaiting obs_rd item.", UVM_HIGH)
        cfg.wait_fifo_not_empty(target_mode_rd_obs_fifo);
        `uvm_info(`gfn, "obs_rd item has arrived, not yet popping from stack.", UVM_HIGH)
      end
      begin
        `uvm_info(`gfn, "Awaiting exp_rd item.", UVM_HIGH)
        cfg.wait_fifo_not_empty(target_mode_rd_exp_fifo);
        `uvm_info(`gfn, "exp_rd item has arrived, not yet popping from stack.", UVM_HIGH)
      end
    join
    begin
      i2c_item temp;
      target_mode_rd_obs_fifo.get(temp);
      `downcast(obs_rd, temp.clone())
      obs_rd.tran_id = dut_target_obs_read_transfer_id++;
      `uvm_info(`gfn, $sformatf("Got obs_rd item %0d.", obs_rd.tran_id), UVM_HIGH)
    end
    target_mode_rd_exp_fifo.get(exp_rd);
    // Don't use the trans_id from the monitor, use our own local counter value.
    exp_rd.tran_id = dut_target_exp_read_transfer_id++;
    `uvm_info(`gfn, $sformatf("Got exp_rd item %0d.", exp_rd.tran_id), UVM_HIGH)

    // Sample the covergroup before doing the comparison.
    if (cfg.en_cov) begin
      cov.sample_i2c_b2b_cg(obs_rd.addr, `gmv(ral.ctrl.enablehost));
    end

    obs_rd.pname = "obs_rd";
    exp_rd.pname = "exp_rd";
    target_rd_comp(obs_rd, exp_rd);
  endtask: compare_target_read_trans

  // This task compares either read or write transactions for the
  // (DUT/AGENT == Controller/Target) configuration.
  //
  task compare_controller_trans(bus_op_e dir = BusOpWrite);
    i2c_item exp, obs;

    fork
      begin
        // Get OBS item
        case (dir)
          BusOpWrite: controller_mode_wr_obs_fifo.get(obs);
          BusOpRead: controller_mode_rd_obs_fifo.get(obs);
          default:;
        endcase

        // Save the last databyte of the write transaction, as some directed test
        // sequences use it for checking purposes.
        if (dir == BusOpWrite) cfg.lastbyte = obs.data_q[$];

        // If 'seq_cfg.en_rx_overflow' was set, the stimulus has made the RXFIFO overflow,
        // dropping the final byte.
        // The observed item (from the monitor) will have seen the item, but it won't appear
        // on the output of the DUT's RXFIFO, and hence in our exp item.
        if (cfg.seq_cfg.en_rx_overflow && obs.bus_op == BusOpRead) begin
          void'(obs.data_q.pop_back());
          obs.num_data--;
        end
      end
      begin
        `uvm_info(`gfn, $sformatf("Awaiting exp_%0s item.", dir.name()), UVM_HIGH)
        // Get EXP item
        case (dir)
          BusOpWrite: controller_mode_wr_exp_fifo.get(exp);
          BusOpRead: controller_mode_rd_exp_fifo.get(exp);
          default:;
        endcase
        // Increment the counter for each expected DUT-Controller transaction
        exp.tran_id = dut_controller_transfer_id++;
        `uvm_info(`gfn, $sformatf("Got exp_%0s item %0d.", dir.name(), exp.tran_id), UVM_MEDIUM)
      end
    join

    if (cfg.en_cov) begin
      cov.sample_i2c_b2b_cg(obs.addr, `gmv(ral.ctrl.enablehost));
      sample_fmt_fifo_data(obs);
    end

    if (!cfg.en_scb) return; // Skip comparison

    if (!obs.compare(exp)) begin
      `uvm_error(`gfn, $sformatf(
        "Miscompare: DUT-Controller, dir:%0s\n--> EXP:\n%0s\--> OBS:\n%0s",
        dir.name(), exp.sprint(), obs.sprint()))
    end else begin
      `uvm_info(`gfn, $sformatf(
        "Compare succeeded: DUT-Controller, dir:%0s\n--> EXP:\n%0s\--> OBS:\n%0s",
        dir.name(), exp.sprint(), obs.sprint()), UVM_MEDIUM)
    end
  endtask : compare_controller_trans

  // Compare seq_items for DUT-Target Write Transactions
  //
  // Compare start, stop and wdata only
  function void target_wr_comp(i2c_item obs, i2c_item exp);
    string str = (exp.start) ? "addr" : (exp.stop) ? "stop" : "";
    `uvm_info(`gfn, $sformatf("target_wr_comp() exp_wr_txn (%0s) %0d\n%s",
      str, exp.tran_id, exp.sprint()), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("target_wr_comp() obs_wr_txn (%0s) %0d\n%s",
      str, obs.tran_id, obs.sprint()), UVM_MEDIUM)

    `DV_CHECK_EQ(obs.tran_id, exp.tran_id)
    `DV_CHECK_EQ(obs.start, exp.start)
    `DV_CHECK_EQ(obs.stop, exp.stop)
    if (obs.stop == 0 && obs.rstart == 0) begin
      `DV_CHECK_EQ(obs.wdata, exp.wdata)
    end
  endfunction: target_wr_comp

  // Compare seq_items for DUT-Target Read Transactions
  //
  function void target_rd_comp(i2c_item obs, i2c_item exp);
    `uvm_info(`gfn, $sformatf("target_rd_comp() exp_rd_txn %0d\n%s",
      exp.tran_id, exp.sprint()), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("target_rd_comp() obs_rd_txn %0d\n%s",
      obs.tran_id, obs.sprint()), UVM_MEDIUM)

    `DV_CHECK_EQ(obs.tran_id, exp.tran_id)
    `DV_CHECK_EQ(obs.num_data, exp.num_data)
    `DV_CHECK_EQ(obs.data_q.size(), exp.data_q.size())

    foreach (exp.data_q[i]) begin
      `DV_CHECK_EQ(obs.data_q[i], exp.data_q[i])
    end
  endfunction: target_rd_comp

  // Reset local fifos, queues and variables
  virtual function void reset(string kind = "HARD");
    super.reset(kind);

    cfg.scoreboard.reset_dut_target_wr_compare.trigger();
    cfg.scoreboard.reset_dut_target_rd_compare.trigger();

    dut_target_exp_read_transfer_id = 0;
    dut_target_obs_read_transfer_id = 0;
    dut_target_exp_write_transfer_id = 0;
    dut_target_obs_write_transfer_id = 0;
    dut_controller_transfer_id = 0;
    controller_mode_wr_exp_fifo.flush();
    controller_mode_wr_obs_fifo.flush();
    controller_mode_rd_exp_fifo.flush();
    controller_mode_rd_obs_fifo.flush();
    target_mode_wr_exp_fifo.flush();
    target_mode_wr_obs_fifo.flush();
    target_mode_rd_exp_fifo.flush();
    target_mode_rd_obs_fifo.flush();
    fmt_fifo_data_q.delete();

    // Also reset the model when the scoreboard is reset (such as on dut_init())
    model.reset();
  endfunction : reset

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(i2c_item, controller_mode_rd_obs_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(i2c_item, controller_mode_wr_obs_fifo)
  endfunction

  function void report_phase(uvm_phase phase);
    super.report_phase(phase);

    `uvm_info(`gfn, $sformatf("report_phase() i2c_env_cfg:\n%s", cfg.convert2string()), UVM_MEDIUM)

    if (cfg.en_scb) begin
      string str = {$sformatf("\nSCOREBOARD REPORT_PHASE\n")};
      `uvm_info(`gfn, $sformatf("%s", str), UVM_MEDIUM)
    end
  endfunction : report_phase

endclass : i2c_scoreboard
