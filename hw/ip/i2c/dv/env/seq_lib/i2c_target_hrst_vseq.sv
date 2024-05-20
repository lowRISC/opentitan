// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test to check the DUT-Target behaviour with early assertion of RSTART or STOP
// (We refer to this behaviour as 'glitches' in within this vseq)
//
// The main function of this vseq is to increase coverage of FSM state transitions
// back to the idle/acquire states upon the early Sr/P conditions short-circuiting the
// normal transfer/transaction process.
//
// Test Procedure:
// > Initialize DUT in Target mode
// > Randomly introduce glitches specified by enum `glitch_e`
//   > For each glitch type, byte transmission will be interrupted causing the internal FSM to
//     go to Idle/AcquireStart state
// > Issue new transactions after glitch to check if DUT is processing transactions as expected

class i2c_target_hrst_vseq extends i2c_target_smoke_vseq;

  // Control-flags used to sequence tasks

  // Used to track which call to fetch_txn should avoid appending Start
  bit skip_start = 0;

  rand uint glitch_txn_num; // This indicates the index of the transaction we will glitch

  // Protocol glitch type
  rand glitch_e glitch;
  // 0 - Indicates Start/Stop glitch in Write transaction
  // 1 - Indicates Start/Stop glitch in Read transaction
  rand tran_type_e rw_bit;

  `uvm_object_utils(i2c_target_hrst_vseq)
  `uvm_object_new

  /////////////////
  // CONSTRAINTS //
  /////////////////

  constraint num_trans_c {num_trans == 5;}
  // Constrain the glitched transaction to allow a number of post-glitch normal
  // transactions to test recovery.
  constraint glitch_txn_num_c {glitch_txn_num < num_trans - 2;}

  constraint rw_bit_c {
    // Read state glitches covered in i2c_glitch_vseq
    rw_bit dist {ReadOnly := 0, WriteOnly := 1};
  }
  // Randomize type of glitch based on rw_bit with equal probability
  constraint glitch_c {
     if (rw_bit == ReadOnly) {
       glitch dist {
         ReadDataByteStart := 1,
         ReadDataAckStart := 1,
         ReadDataAckStop := 1
       };
     }
     else{
       glitch dist {
         AddressByteStart := 1,
         AddressByteStop := 1 ,
         WriteDataByteStart := 1 ,
         WriteDataByteStop := 1
       };
     }
     solve rw_bit before glitch;
  }

  ///////////////////
  // CLASS METHODS //
  ///////////////////

  virtual task pre_start();
    super.pre_start();
    expected_intr[UnexpStop] = 1;
  endtask


  virtual task body();
    // Intialize DUT in target mode and agent in controller mode
    initialization();

    `uvm_info("cfg_summary",
              $sformatf("target_addr0:0x%x target_addr1:0x%x illegal_addr:0x%x num_trans:%0d",
                        target_addr0, target_addr1, illegal_addr, num_trans), UVM_MEDIUM)

    fork
      // Send all transaction stimulus
      for (uint i = 0; i < num_trans; i++) send_trans(i);
      // Handle normal interrupts, and gracefully stop interrupt handlers at end of test
      while (!cfg.stop_intr_handler) process_target_interrupts();
      stop_target_interrupt_handler();
    join
  endtask : body


  task send_trans(uint i);
    // Agent-Controller sequence to generate stimulus
    i2c_target_base_seq m_i2c_host_seq;

    `uvm_info(`gfn, $sformatf("start of round %0d/%0d (glitch_txn:%0d)",
                              i + 1, num_trans, glitch_txn_num + 1), UVM_MEDIUM)

    // Wait for previous stop-condition before proceeding with next transaction.
    if (i > 0) begin
      `DV_WAIT(cfg.m_i2c_agent_cfg.got_stop,, cfg.spinwait_timeout_ns, "target_hrst_vseq")
      cfg.m_i2c_agent_cfg.got_stop = 0;
    end

    // If the glitched transaction was a Read, reset the DUT's TXFIFO after completion.
    // This ensures there is no stale data left in the fifo for the next read transaction.
    if (i == (glitch_txn_num + 1) && rw_bit == ReadOnly) begin
      ral.fifo_ctrl.txrst.set(1'b1);
      csr_update(ral.fifo_ctrl);
    end

    // Apply a new set of timing parameters for the next transaction.
    // However, don't update new timing params during and right after the glitched runt transaction
    if (!(i inside {glitch_txn_num, (glitch_txn_num + 1)})) begin
      get_timing_values();
      program_registers();
    end

    // Populate item queue that defines the upcoming transaction
    `uvm_create_obj(i2c_target_base_seq, m_i2c_host_seq)
    if (i == glitch_txn_num) begin
      `uvm_info(`gfn, $sformatf("Creating glitched transaction stimulus as trans %0d/%0d",
        i+1, num_trans), UVM_MEDIUM)
      // This special routine creates the glitched transaction
      fetch_no_tb_txn(m_i2c_host_seq.req_q);
    end else begin
      // Create a normal transaction
      i2c_item txn_q[$];
      create_txn(txn_q);
      fetch_txn(txn_q, m_i2c_host_seq.req_q, .skip_start(skip_start));
    end

    fork
      // Start stimulus sequence
      m_i2c_host_seq.start(p_sequencer.i2c_sequencer_h);
      if (i == glitch_txn_num) fork
        // Reset the monitor state just before the glitch is introduced.
        reset_monitor();
        // Wait for completion of the glitch transaction, and cleanup the scoreboard for further
        // transactions to test recovery.
        cleanup_scoreboard();
      join
    join_any

    `uvm_info("seq", $sformatf("End of round %0d/%0d", i + 1, num_trans), UVM_MEDIUM)

    // Reset 'skip_start' the iteration after the glitched transaction
    if (i == (glitch_txn_num + 1)) skip_start = 0;

    sent_txn_cnt++;
  endtask: send_trans


  // We need to reset some of the monitor state just before introducing the 'glitch' condition,
  // as the environment is currently incapable of modelling this behaviour precisely.
  // During data transmission, the glitch is introduced on a random bit using the
  // <i2c_item>.wait_cycles field. The monitor state should be reset before the earliest
  // possible cycle a glitch may be introduced.
  //
  task reset_monitor();
    // The 'wait_cycles' variable indicates at which point the monitor should be reset.
    // - For AddressByteStart the minimum is 1 cycle
    // - For AddressByteStop, the minimum is 9 cycles (Start+Address+ACK).
    // To prevent TB side races, +1 is added to these limits.

    int wait_cycles = glitch inside {AddressByteStart, AddressByteStop} ? 2 : 10;
    repeat(wait_cycles) @(posedge cfg.m_i2c_agent_cfg.vif.scl_i);

    `uvm_info(`gfn, "Issuing monitor_rst now.", UVM_MEDIUM)
    cfg.m_i2c_agent_cfg.monitor_rst = 1;

    cfg.clk_rst_vif.wait_clks(2);

    `uvm_info(`gfn, "Clearing monitor_rst now.", UVM_MEDIUM)
    cfg.m_i2c_agent_cfg.monitor_rst = 0;
  endtask: reset_monitor


  task cleanup_scoreboard();
    // We're now driving the glitched transaction. After the expected item is sent
    // to the scoreboard, wait until the queue becomes empty, indicating the scoreboard has
    // popped the item for comparison.

    fork
      if (!cfg.scoreboard.target_mode_wr_exp_fifo.is_empty()) begin
        `uvm_info(`gfn, "Waiting for target_mode_wr_exp_fifo to become empty.", UVM_MEDIUM)
        `DV_SPINWAIT(// WAIT_
                     cfg.wait_fifo_not_empty(cfg.scoreboard.target_mode_wr_exp_fifo);,
                     // MSG_
                     "Timed-out waiting for target_mode_wr_exp_fifo to become empty.",
                     // TIMEOUT_NS_
                     cfg.spinwait_timeout_ns)

        // Reset the scoreboard checking routine
        `uvm_info(`gfn, "target_mode_wr_exp_fifo is empty. Resetting the scb checking routine now.",
                  UVM_MEDIUM)
        cfg.scoreboard.reset_dut_target_wr_compare.trigger();
      end
      if (!cfg.scoreboard.target_mode_rd_exp_fifo.is_empty()) begin
        `uvm_info(`gfn, "Waiting for target_mode_rd_exp_fifo to become empty.", UVM_MEDIUM)
        `DV_SPINWAIT(// WAIT_
                     cfg.wait_fifo_not_empty(cfg.scoreboard.target_mode_rd_exp_fifo);,
                     // MSG_
                     "Timed-out waiting for target_mode_rd_exp_fifo to become empty.",
                     // TIMEOUT_NS_
                     cfg.spinwait_timeout_ns)

        // Reset the scoreboard checking routine
        `uvm_info(`gfn, "target_mode_rd_exp_fifo is empty. Resetting the scb checking routine now.",
                  UVM_MEDIUM)
        cfg.scoreboard.reset_dut_target_rd_compare.trigger();
      end
    join

  endtask: cleanup_scoreboard


  // Populate transaction queue with glitches based on glitch variable
  task fetch_no_tb_txn(ref i2c_item dst_q[$]);

    // Make sure error txn is long enough to have various different transaction segments
    cfg.min_data = 20;
    // Disable address randomization for the glitch txn
    cfg.bad_addr_pct = 0;

    // Add 'START' to the front
    begin
      i2c_item txn;
      `uvm_create_obj(i2c_item, txn)
      txn.drv_type = HostStart;
      dst_q.push_back(txn);
    end

    `uvm_info(`gfn, $sformatf("Glitching a %0s transaction", rw_bit ? "Read" : "Write"), UVM_MEDIUM)
    case (rw_bit)
      ReadOnly: create_read_glitch(dst_q);
      WriteOnly: create_write_glitch(dst_q);
      default:;
    endcase

    // If we glitched with an unexpected start condition, we don't need to create
    // a start condition for the next stimulus transaction that tests recovery. So skip it.
    if (glitch == AddressByteStart) skip_start = 1;

  endtask


  // Populate transaction queue to introduce Start/Stop conditions in Write Data/Address byte
  function void create_write_glitch(ref i2c_item driver_q[$]);
    i2c_item txn;
    i2c_item exp_txn;
    `uvm_info(`gfn, $sformatf("Introducing %s glitch", glitch.name()), UVM_LOW)

    // Address byte
    `uvm_create_obj(i2c_item, txn)
    txn.wdata[7:1] = get_target_addr(); // target_addr0;
    txn.wdata[0] = (rw_bit == ReadOnly); // dir
    txn.drv_type = HostData;
    driver_q.push_back(txn);

    `uvm_create_obj(i2c_item, exp_txn)
    exp_txn.wdata = txn.wdata;


    // Add entry for Address glitch
    if (glitch inside {AddressByteStart, AddressByteStop}) begin

      i2c_item glitch_txn;
      `uvm_create_obj(i2c_item, glitch_txn)
      case (glitch)
        AddressByteStart: glitch_txn.drv_type = HostRStart; // Add Start glitch
        AddressByteStop: glitch_txn.drv_type = HostStop; // Add Stop glitch
        default:;
      endcase
      driver_q.push_back(glitch_txn);

      // There should be no entry in the ACQ FIFO for an AddressByte*
      // glitch, since this is a new transaction that never completes
      // addressing the target.
      return; // return, since glitch entry is done

    end else begin
      // for valid address transaction, indicate start bit
      exp_txn.start = 1;
      push_exp_txn(exp_txn);
    end

    // Data byte
    `uvm_create_obj(i2c_item, txn)
    txn.wdata = $urandom_range(1, 127);

    `uvm_create_obj(i2c_item, exp_txn)
    exp_txn.wdata = 8'hDD;

    // Glitch in Data byte
    if (glitch inside {WriteDataByteStart, WriteDataByteStop}) begin
      txn.drv_type = HostDataNoWaitForACK;
      txn.wait_cycles = $urandom_range(2, 6);
      if (glitch == WriteDataByteStart) begin
        txn.wdata = 8'hFF;
      end else if (glitch == WriteDataByteStop) begin
        txn.wdata = 8'h00;
      end
      // Push transaction to driver queue
      driver_q.push_back(txn);
      // Add glitch transaction
      `uvm_create_obj(i2c_item, txn)
      if (glitch == WriteDataByteStart) begin
        txn.drv_type = HostRStart;
        txn.rstart = 1;
        skip_start = 1;
      end else begin
        txn.drv_type = HostStop;
        txn.stop = 1;
        exp_txn.stop = 1;
      end
      // Push transaction for driver
      driver_q.push_back(txn);
    end
    // Push transaction for expected ACQ data
    // No need to do this with skip_start, since it would duplicate fetch_txn()
    // Is this horrible spaghetti code? Why, yes, yes it is.
    // TODO(): Cleanup?
    if (!skip_start) begin
      push_exp_txn(exp_txn);
    end
  endfunction


  task create_read_glitch(ref i2c_item driver_q[$]);
    i2c_item txn;
    i2c_item full_txn;
    i2c_item read_txn;
    i2c_item exp_txn;
    bit valid_addr;
    bit got_valid;
    `uvm_info(`gfn, $sformatf("Introducing %s glitch", glitch.name()), UVM_LOW)
    // Address byte
    `uvm_create_obj(i2c_item, txn)
    `uvm_create_obj(i2c_item, full_txn)
    `uvm_create_obj(i2c_item, exp_txn)
    txn.wdata[7:1] = get_target_addr(); //target_addr0;
    txn.wdata[0] = rw_bit == ReadOnly;
    txn.read = rw_bit == ReadOnly;
    txn.drv_type = HostData;
    txn.tran_id = this.tran_id;
    full_txn.start = 1;
    full_txn.tran_id = this.exp_rd_id;
    `downcast(exp_txn, txn.clone());
    valid_addr = is_target_addr(txn.wdata[7:1]);
    // Push transaction for driver
    driver_q.push_back(txn);
    // Update expected transaction for address
    exp_txn.start = 1;
    exp_txn.read = 1;
    push_exp_txn(exp_txn);
    // Update read transasction count
    if (valid_addr) this.exp_rd_id++;
    // Update read transaction of DUT
    `uvm_create_obj(i2c_item, read_txn)
    read_txn.wdata = 8'hFF;
    read_rcvd.push_back(1); // add one entry for txfifo
    read_txn_q.push_back(read_txn);
    // Data byte
    if(glitch inside {ReadDataByteStart}) begin
      // Update driver transaction
      `uvm_create_obj(i2c_item, txn)
      txn.drv_type = HostWait;
      txn.wait_cycles = $urandom_range(1, 6);
      // Clear TXDATA FIFO
      ral.fifo_ctrl.txrst.set(1'b1);
      csr_update(ral.fifo_ctrl);
      cfg.clk_rst_vif.wait_clks(1);
      // Write 'hFF to TXDATA FIFO so that SDA is driven high
      csr_wr(.ptr(ral.txdata), .value('hFF));
      cfg.clk_rst_vif.wait_clks(1);
      // Push transaction to driver
      driver_q.push_back(txn);
      // Introduce Start glitch
      `uvm_create_obj(i2c_item, txn)
      txn.drv_type = HostRStart;
      // Push glitch transaction to driver
      driver_q.push_back(txn);
      // Update expected transaction
      `uvm_create_obj(i2c_item, exp_txn)
      exp_txn.wdata = 8'hDD;
      exp_txn.rstart = 1;
      push_exp_txn(exp_txn);
      skip_start = 1;
      full_txn.rstart = 1;
      if (valid_addr) p_sequencer.target_mode_rd_exp_port.write(full_txn);
      return;
    end else if (glitch inside {ReadDataAckStart, ReadDataAckStop}) begin
      // Update driver transaction
      `uvm_create_obj(i2c_item, txn)
      txn.drv_type = HostWait;
      txn.wait_cycles = 8; // Wait for full byte transmission
      // Push transaction to driver
      driver_q.push_back(txn);
      // Introduce Start glitch
      `uvm_create_obj(i2c_item, txn)
      `uvm_create_obj(i2c_item, exp_txn)
      exp_txn.wdata = 8'hDD;
      if (glitch inside {ReadDataAckStart}) begin
        txn.drv_type = HostRStart;
        exp_txn.rstart = 1;
        skip_start = 1;
        full_txn.rstart = 1;
      end else begin
        txn.drv_type = HostStop;
        exp_txn.stop = 1;
        full_txn.stop = 1;
      end
      // Push glitch transaction to driver
      driver_q.push_back(txn);
      // push expected transaction
      push_exp_txn(exp_txn);
      if (valid_addr) p_sequencer.target_mode_rd_exp_port.write(full_txn);
    end
  endtask


  // Update expected transaction from ACQDATA register
  function void push_exp_txn(ref i2c_item exp_txn);
    // Push transaction for expected ACQ data
    p_sequencer.target_mode_wr_exp_port.write(exp_txn);
    exp_txn.tran_id = this.tran_id;
    cfg.sent_acq_cnt++;
    this.tran_id++;
  endfunction


  task stop_target_interrupt_handler();
    string id = "stop_interrupt_handler";
    int    acq_rd_cyc;
    acq_rd_cyc = 9 * (thigh + tlow);
    `DV_WAIT(cfg.sent_acq_cnt > 0,, cfg.spinwait_timeout_ns, id)
    `DV_WAIT(sent_txn_cnt == num_trans,, cfg.long_spinwait_timeout_ns, id)
    cfg.read_all_acq_entries = 1;
    if (cfg.rd_pct != 0) begin
      `DV_WAIT(cfg.m_i2c_agent_cfg.sent_rd_byte > 0,, cfg.spinwait_timeout_ns, id)
      `uvm_info(id, $sformatf("st3 sent_acq:%0d rcvd_acq:%0d",
                              cfg.sent_acq_cnt, cfg.rcvd_acq_cnt), UVM_HIGH)
    end
    `DV_WAIT(cfg.sent_acq_cnt <= cfg.rcvd_acq_cnt,, cfg.spinwait_timeout_ns, id)
    csr_spinwait(.ptr(ral.status.acqempty), .exp_data(1'b1));

    // add drain time before stop interrupt handler
    cfg.clk_rst_vif.wait_clks(1000);
    // Add extra draintime for tx overflow test
    cfg.stop_intr_handler = 1;
    `uvm_info(id, "called stop_intr_handler", UVM_MEDIUM)
  endtask // stop_target_interrupt_handler

endclass : i2c_target_hrst_vseq
