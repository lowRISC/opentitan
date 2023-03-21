// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Host agent reset test
class i2c_target_hrst_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_hrst_vseq)
  `uvm_object_new

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
    bit is_read;

    // Add some config noise to stretch coverage
    ral.ctrl.enablehost.set(1'b0);
    ral.ctrl.enabletarget.set(1'b1);
    csr_update(ral.ctrl);
    ral.ctrl.enablehost.set(1'b1);
    ral.ctrl.enabletarget.set(1'b0);
    csr_update(ral.ctrl);

    // Intialize dut in device mode and agent in host mode
    initialization(Device);
    `uvm_info("cfg_summary",
              $sformatf("target_addr0:0x%x target_addr1:0x%x illegal_addr:0x%x num_trans:%0d",
                        target_addr0, target_addr1, illegal_addr, num_trans), UVM_MEDIUM)
    print_time_property();

    fork
      begin
        `uvm_info(`gfn, $sformatf("num_trans:%0d", num_trans), UVM_MEDIUM)
        num_trans = 5;
        reset_txn_num = $urandom_range(1, 3);

        for (int i = 0; i < num_trans; i++) begin
          `uvm_info("seq", $sformatf("round %0d reset_txn_num:%0d", i, reset_txn_num), UVM_MEDIUM)
          if (i > 0) begin
            // wait for previous stop before program a new timing param.
            `DV_WAIT(cfg.m_i2c_agent_cfg.got_stop,, cfg.spinwait_timeout_ns, "target_hrst_vseq")
            cfg.m_i2c_agent_cfg.got_stop = 0;
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
          if (i == reset_txn_num) begin
            `uvm_info("seq", $sformatf("test skip comparison is set %0d", i), UVM_HIGH)
            reset_drv_st = 1;
            fetch_no_tb_txn(txn_q, m_i2c_host_seq.req_q, is_read);
            if(is_read)
              `uvm_info(`gfn, "Injecting Start glitch in Read data", UVM_LOW)
            else
              `uvm_info(`gfn, "Injecting Start glitch in Write data", UVM_LOW)
          end else begin
            fetch_txn(txn_q, m_i2c_host_seq.req_q);
          end
          m_i2c_host_seq.start(p_sequencer.i2c_sequencer_h);
          if (i == reset_txn_num) begin
            resume_sb = 1;
            `uvm_info("seq", $sformatf("resume test comparison %0d", i), UVM_HIGH)
          end

          sent_txn_cnt++;
        end
      end
      process_target_interrupts();
      stop_target_interrupt_handler();
      begin
        `DV_WAIT(reset_drv_st,, cfg.spinwait_timeout_ns, "tb_comp_off")
        while (!cfg.scb_h.target_mode_wr_exp_fifo.is_empty()) begin
          cfg.clk_rst_vif.wait_clks(1);
        end
        cfg.scb_h.skip_target_txn_comp = 1;
        while (!cfg.scb_h.target_mode_rd_exp_fifo.is_empty()) begin
          cfg.clk_rst_vif.wait_clks(1);
        end
        cfg.scb_h.skip_target_rd_comp = 1;
        `DV_WAIT(resume_sb,, cfg.spinwait_timeout_ns, "resume_sb")
      end
      begin
        if (is_read) begin
          `DV_WAIT(reset_drv_st,, cfg.spinwait_timeout_ns, "set hot_glitch")
          repeat(13) // Start+Address+RW+DATA0
            @(posedge cfg.m_i2c_agent_cfg.vif.scl_i);
          cfg.m_i2c_agent_cfg.hot_glitch = 1;
          `DV_WAIT(!cfg.m_i2c_agent_cfg.hot_glitch,, cfg.spinwait_timeout_ns, "unset hot_glitch")
        end
      end
    join
  endtask : body

  // Feed txn to driver only. This doesn't create expected txn.
  function void fetch_no_tb_txn(ref i2c_item src_q[$], i2c_item dst_q[$], bit is_read);
    i2c_item txn;
    i2c_item rs_txn;
    i2c_item exp_txn;
    i2c_item full_txn;
    int read_size;
    bit [6:0] t_addr;
    bit valid_addr;
    bit got_valid;

    `uvm_info("seq", $sformatf("ntb idx %0d:is_read:%0b size:%0d fetch_txn:%0d",
                               start_cnt++, is_read, src_q.size(), full_txn_num++), UVM_MEDIUM)
    // Update read/write bit for the address transaction
    is_read = get_read_write();

    // From target mode, read data is corresponds to txdata from DUT.
    // While dut's sda is always 1, tb can drive sda freely.
    // Update read data to all 1's to recevie any incoming data bits.
    update_rd_data(is_read, src_q);
    print_wr_data(is_read, src_q);
    `uvm_create_obj(i2c_item, full_txn)

    // Add 'START' to the front
    `uvm_create_obj(i2c_item, txn)
    txn.drv_type = HostStart;
    dst_q.push_back(txn);
    full_txn.start = 1;
    if (is_read) full_txn.tran_id = this.exp_rd_id;
    // Address
    `uvm_create_obj(i2c_item, txn)
    `uvm_create_obj(i2c_item, exp_txn)
    txn.drv_type = HostData;
    txn.start = 1;
    txn.wdata[7:1] = get_target_addr(); //target_addr0;
    txn.wdata[0] = is_read;
    valid_addr = is_target_addr(txn.wdata[7:1]);

    txn.tran_id = this.tran_id;
    `downcast(exp_txn, txn.clone());
    dst_q.push_back(txn);
    full_txn.addr = txn.wdata[7:1];
    full_txn.read = is_read;
    // Start command acq entry
    if (valid_addr && !is_read) begin
      p_sequencer.target_mode_wr_exp_port.write(exp_txn);
      cfg.sent_acq_cnt++;
      this.tran_id++;
      got_valid = 1;
      if (is_read) this.exp_rd_id++;
      // Add entry for RSTART glitch
      `uvm_create_obj(i2c_item, exp_txn)
      exp_txn.tran_id = this.tran_id;
      exp_txn.rstart=1;
      exp_txn.start=0;
      exp_txn.stop=0;
      p_sequencer.target_mode_wr_exp_port.write(exp_txn);
      cfg.sent_acq_cnt++;
      this.tran_id++;
    end

    `uvm_create_obj(i2c_item, txn)
    txn = src_q.pop_front();
    txn.drv_type = HostData;
    txn.rstart = 0;
    if (valid_addr && !is_read) begin
      // For Write transactions in Target mode, since I2C driver is issuing data bytes,
      // Filling up the queue with one data item would be sufficient
      txn.drv_type = HostDataGlitch;
      dst_q.push_back(txn);
      return;
    end

    // Start command acq entry
    read_size = get_read_data_size(src_q, is_read, read_rcvd);

    // Data
    while (src_q.size() > 0) begin
      `uvm_create_obj(i2c_item, txn)
      txn = src_q.pop_front();
      if (txn.drv_type != HostRStart) begin
        // Restart only has empty data for address holder
        full_txn.data_q.push_back(txn.wdata);
      end

      // RS creates 2 extra acq entry
      // one for RS
      // the other for a new start acq_entry with address
      if (txn.drv_type == HostRStart) begin
        bit prv_read = 0;
        bit prv_valid = valid_addr;

        t_addr = get_target_addr();
        valid_addr = is_target_addr(t_addr);

        `uvm_create_obj(i2c_item, rs_txn)
        `downcast(rs_txn, txn.clone())
        dst_q.push_back(txn);

        rs_txn.drv_type = HostData;
        rs_txn.start = 1;
        rs_txn.rstart = 0;
        rs_txn.wdata[7:1] = t_addr;
        prv_read = is_read;
        is_read = rs_txn.read;
        rs_txn.wdata[0] = is_read;
        dst_q.push_back(rs_txn);

        // fetch previous full_txn and creat a new one
        if (prv_read) begin
          full_txn.stop = 1;
        end
        `uvm_create_obj(i2c_item, full_txn)
        `downcast(full_txn, rs_txn);
        if (is_read) begin
          full_txn.tran_id = exp_rd_id;
        end
      end else begin
        if (is_read) begin
          i2c_item read_txn;
          `uvm_create_obj(i2c_item, read_txn)
          `downcast(read_txn, txn.clone())
          full_txn.num_data++;
          if (src_q.size() == 0) begin
            txn.drv_type = get_eos(.is_stop(1));
          end else begin
            // if your next item is restart Do nack
            if (src_q[0].drv_type == HostRStart) txn.drv_type = get_eos();
            else txn.drv_type = HostAck;
          end
          if (!cfg.use_drooling_tx) read_txn_q.push_back(read_txn);
        end

        dst_q.push_back(txn);

      end
    end // while (src_q.size() > 0)

    // Stop
    `uvm_create_obj(i2c_item, txn)
    txn.tran_id = this.tran_id;
    txn.stop = 1;
    txn.drv_type = HostStop;
    dst_q.push_back(txn);
    full_txn.stop = 1;
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

  // Replace read data to all 1's.
  function void update_rd_data(bit is_read, ref i2c_item myq[$]);
    bit read = is_read;
    foreach (myq[i]) begin
      if (myq[i].rstart) begin
        read = myq[i].read;
      end else begin
        if (read) myq[i].wdata = 8'hff;
      end
    end
  endfunction

endclass : i2c_target_hrst_vseq
