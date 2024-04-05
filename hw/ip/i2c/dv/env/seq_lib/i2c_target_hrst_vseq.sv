// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test to check the behaviour of DUT in case of RSTART or STOP githces in Target mode
// Sequence:
// > Initialize DUT in Target mode
// > Randomly introduce glitches specified by enum `glitch_e`
//   > For each gltich type, byte transmission will be interrupted causing the internal FSM to
//     go to Idle/AcquireStart state
// > Issue transactions after glitch to check if DUT is processing transactions as expected

class i2c_target_hrst_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_hrst_vseq)
  `uvm_object_new

  // Protocol glitch type
  rand glitch_e glitch;
  // 0 - Indicates Start/Stop glitch in Write transaction
  // 1 - Indicates Start/Stop glitch in Read transaction
  rand tran_type_e rw_bit;
  // Used to track which call to fetch_txn should avoid appending Start
  bit skip_start;
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

  virtual task pre_start();
    super.pre_start();
    expected_intr[UnexpStop] = 1;
  endtask

  virtual task body();
    i2c_target_base_seq m_i2c_host_seq;
    i2c_item txn_q[$];
    int reset_txn_num = 1;
    bit reset_drv_st = 0;
    bit resume_sb = 0;

    // Add some config noise to stretch coverage
    ral.ctrl.enablehost.set(1'b0);
    ral.ctrl.enabletarget.set(1'b1);
    csr_update(ral.ctrl);
    ral.ctrl.enablehost.set(1'b1);
    ral.ctrl.enabletarget.set(1'b0);
    csr_update(ral.ctrl);
    skip_start = 0;

    // Intialize dut in device mode and agent in host mode
    initialization();
    `uvm_info("cfg_summary",
              $sformatf("target_addr0:0x%x target_addr1:0x%x illegal_addr:0x%x num_trans:%0d",
                        target_addr0, target_addr1, illegal_addr, num_trans), UVM_MEDIUM)
    fork
      begin
        `uvm_info(`gfn, $sformatf("num_trans:%0d", num_trans), UVM_MEDIUM)
        num_trans = 5;
        reset_txn_num = $urandom_range(1, 3);

        for (int i = 0; i < num_trans; i++) begin
          `uvm_info("seq", $sformatf("round %0d reset_txn_num:%0d", i, reset_txn_num), UVM_MEDIUM)
          if (i > 0) begin
            // Wait for previous stop before proceeding with next sequence.
            `DV_WAIT(cfg.m_i2c_agent_cfg.got_stop,, cfg.spinwait_timeout_ns, "target_hrst_vseq")
            cfg.m_i2c_agent_cfg.got_stop = 0;
            // Reset i2c.TXDATA fifo after completion of glitch transaction
            if (i == reset_txn_num + 1 && rw_bit == ReadOnly) begin
              ral.fifo_ctrl.txrst.set(1'b1);
              csr_update(ral.fifo_ctrl);
            end
          end
          // exclude timing param update during and right after runt transaction
          if (!(i inside {reset_txn_num, (reset_txn_num + 1)})) begin
            get_timing_values();
            program_registers();
          end
          `uvm_create_obj(i2c_target_base_seq, m_i2c_host_seq)

          // Make sure error txn has long enough to have various transaction segment
          if (i == reset_txn_num) begin
            cfg.min_data = 20;
          end
          create_txn(txn_q);
          // Populate transaction queue
          if (i == reset_txn_num) begin
            `uvm_info("seq", $sformatf("test skip comparison is set %0d", i), UVM_HIGH)
            reset_drv_st = 1;
            fetch_no_tb_txn(m_i2c_host_seq.req_q);
          end else begin
            fetch_txn(txn_q, m_i2c_host_seq.req_q, .skip_start(skip_start));
          end
          // Start sequence
          fork
            begin : main_thread
              m_i2c_host_seq.start(p_sequencer.i2c_sequencer_h);
            end : main_thread
            begin : monitor_reset
              if (i == reset_txn_num) begin
                // Wait until just before glitch is introduced and then issue monitor reset
                // Wait_cycles variable indicates at which point monitor on TB has to be reset.
                // During data transmission, glitch is introduced on a random bit using
                //   <i2c_item>.wait_cycles
                // So, monitor should be reset before the earliest glitch cycle.
                // - For AddressByteStart the minimum is 1 cycle
                // - For AddressByteStop, the minimum is 9 cycles (Start+Address+ACK).
                // To prevent TB side races, +1 is added to these limits.
                int wait_cycles = glitch inside {AddressByteStart, AddressByteStop} ? 2 : 10;
                repeat(wait_cycles) @(posedge cfg.m_i2c_agent_cfg.vif.scl_i);
                `uvm_info(`gfn, "Issue monitor_rst", UVM_MEDIUM)
                // Reset monitor
                cfg.m_i2c_agent_cfg.monitor_rst = 1;
                cfg.clk_rst_vif.wait_clks(2);
                cfg.m_i2c_agent_cfg.monitor_rst = 0;
                `uvm_info(`gfn, "Clear monitor_rst", UVM_MEDIUM)
              end
            end : monitor_reset
          join
          // reset skip_start after reset_txn_num+1 iteration
          if (i > reset_txn_num) begin
            skip_start = 0;
          end
          if (i == reset_txn_num) begin
            resume_sb = 1;
            `uvm_info("seq", $sformatf("resume test comparison %0d", i), UVM_HIGH)
          end
          sent_txn_cnt++;
        end
      end
      process_target_interrupts();
      stop_target_interrupt_handler();
      // Wait for completion of all transactions issued in the sequence
      begin
        `DV_WAIT(reset_drv_st,, cfg.spinwait_timeout_ns, "tb_comp_off")
        `DV_SPINWAIT(while (!cfg.scb_h.target_mode_wr_exp_fifo.is_empty()) begin
                       cfg.clk_rst_vif.wait_clks(1);
                     end,
                     $sformatf("timed out waiting for target_mode_wr_exp_fifo size:%0d",
                       cfg.scb_h.target_mode_wr_exp_fifo.used()),
                     cfg.spinwait_timeout_ns)
        cfg.scb_h.skip_target_txn_comp = 1;
        `DV_SPINWAIT(while (!cfg.scb_h.target_mode_rd_exp_fifo.is_empty()) begin
                       cfg.clk_rst_vif.wait_clks(1);
                     end,
                     $sformatf("timed out waiting for target_mode_rd_exp_fifo size:%0d",
                       cfg.scb_h.target_mode_rd_exp_fifo.used()),
                     cfg.spinwait_timeout_ns)
        cfg.scb_h.skip_target_rd_comp = 1;
        `DV_WAIT(resume_sb,, cfg.spinwait_timeout_ns, "resume_sb")
      end
    join
  endtask : body

  // Update expected transaction from ACQDATA register
  function void push_exp_txn(ref i2c_item exp_txn);
    // Push transaction for expected ACQ data
    p_sequencer.target_mode_wr_exp_port.write(exp_txn);
    exp_txn.tran_id = this.tran_id;
    cfg.sent_acq_cnt++;
    this.tran_id++;
  endfunction

  // Populate transaction queue to introduce Start/Stop conditions in Write Data/Address byte
  function void create_write_glitch(ref i2c_item driver_q[$]);
    i2c_item txn;
    i2c_item exp_txn;
    bit valid_addr;
    bit got_valid;
    `uvm_info(`gfn, $sformatf("Introducing %s glitch", glitch.name()), UVM_LOW)
    // Address byte
    `uvm_create_obj(i2c_item, txn)
    `uvm_create_obj(i2c_item, exp_txn)
    txn.wdata[7:1] = get_target_addr(); //target_addr0;
    txn.wdata[0] = rw_bit == ReadOnly;
    txn.drv_type = HostData;
    valid_addr = is_target_addr(txn.wdata[7:1]);
    exp_txn.wdata = txn.wdata;
    // Push transaction to driver queue
    driver_q.push_back(txn);
    // Update glitch data
    if (glitch inside {AddressByteStart, AddressByteStop}) begin
      i2c_item  glitch_txn;
      txn.wait_cycles = $urandom_range(2,6);
      // Add entry for Address glitch
      `uvm_create_obj(i2c_item, glitch_txn)
      if (glitch == AddressByteStart) begin
        txn.wdata = 8'hFF;
        // Add Start glitch
        glitch_txn.drv_type = HostRStart;
        skip_start = 1;
      end else begin
        txn.wdata = 8'h00;
        // Add Stop glitch
        glitch_txn.drv_type = HostStop;
      end
      // Push transaction for driver
      driver_q.push_back(glitch_txn);
      // There should be no entry in the ACQ FIFO for an AddressByte*
      // glitch, since this is a new transaction that never completes
      // addressing the target.
      return; // return, since glitch entry is done
    end else begin
      // for valid address transaction indicate start bit
      txn.start = 1;
      exp_txn.start = 1;
      push_exp_txn(exp_txn);
    end
    // Data byte
    `uvm_create_obj(i2c_item, txn)
    `uvm_create_obj(i2c_item, exp_txn)
    txn.wdata = $urandom_range(1, 127);
    exp_txn.wdata = 8'hDD;
    // Glitch in Data byte
    if (glitch inside {WriteDataByteStart, WriteDataByteStop}) begin
      txn.drv_type = HostDataNoWaitForACK;
      txn.wait_cycles = $urandom_range(2, 6);
      if(glitch == WriteDataByteStart) begin
        txn.wdata = 8'hFF;
      end else if (glitch == WriteDataByteStop) begin
        txn.wdata = 8'h00;
      end
      // Push transaction to driver queue
      driver_q.push_back(txn);
      // Add glitch transaction
      `uvm_create_obj(i2c_item, txn)
      if(glitch == WriteDataByteStart) begin
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

  // Populate transaction queue with glitches based on glitch variable
  task fetch_no_tb_txn(ref i2c_item dst_q[$]);
    i2c_item txn;
    cfg.bad_addr_pct = 0; // Disable address randomization
    `uvm_info("seq", $sformatf("rw_bit:%0b ", bit'(rw_bit)), UVM_MEDIUM)

    // Add 'START' to the front
    `uvm_create_obj(i2c_item, txn)
    txn.drv_type = HostStart;
    dst_q.push_back(txn);

    if (rw_bit == ReadOnly) begin
      create_read_glitch(dst_q);
    end else begin
      create_write_glitch(dst_q);
    end
  endtask

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
