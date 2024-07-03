// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Collects sequence items from observed I2C bus transactions.
//
// Read and Write transactions are collected into different ports, and also
// different ports are used depending on if the Agent itself is configured as
// either a Controller or Target.
// Agent-Target
// W -> 'wr_item_port'
// R -> 'rd_item_port'
// Agent-Controller
// W ->
// R -> 'analysis_port'
//
// Intermediate seq_items are written to the 'req_analysis_port', which become
// available to sequences via the p_sequencer.req_analysis_fifo handle.
// This is used to implement reactive agent sequences.
//
//
// Methods
//
// > Agent-Controller (cfg.if_mode == Host)
// controller_collect_thread()
// controller_address_thread(), controller_read_thread(), controller_write_thread()
//
// > Agent-Target (cfg.if_mode == Device)
// target_collect_thread()
// target_address_thread(), target_read_thread(), target_write_thread()
//
class i2c_monitor extends dv_base_monitor #(
    .ITEM_T (i2c_item),
    .CFG_T  (i2c_agent_cfg),
    .COV_T  (i2c_agent_cov)
  );
  `uvm_component_utils(i2c_monitor)

  uvm_analysis_port #(i2c_item) wr_item_port;   // used to send complete wr_tran to sb
  uvm_analysis_port #(i2c_item) rd_item_port;   // used to send complete rd_tran to sb

  local i2c_item  mon_dut_item;
  local bit [7:0] mon_data;
  local uint      num_dut_tran = 0;
  bit             mon_rstart = 0;
  bit             target_read_phase = 0;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    wr_item_port  = new("wr_item_port", this);
    rd_item_port  = new("rd_item_port", this);
    mon_dut_item  = i2c_item::type_id::create("mon_dut_item", this);
  endfunction : build_phase

  virtual task wait_for_reset_and_drop_item();
    @(negedge cfg.vif.rst_ni);
    num_dut_tran = 0;
    mon_dut_item.clear_all();

  endtask : wait_for_reset_and_drop_item

  virtual task run_phase(uvm_phase phase);
    wait(cfg.en_monitor);
    wait(cfg.vif.rst_ni);
    if (cfg.if_mode == Host) begin
      fork
        forever controller_collect_thread();
        ack_stop_mon();
      join_none
    end else if (cfg.if_mode == Device) begin
      forever begin
        fork begin: iso_fork
          fork
            target_collect_thread();
            begin // Monitor on-the-fly reset, clear all state if reset asserted
              wait_for_reset_and_drop_item();
              `uvm_info(`gfn, $sformatf("Monitor saw reset assertion, clearing state now:\n%s",
                                        mon_dut_item.sprint()), UVM_DEBUG)
            end
            forever perf_monitor(cfg.vif, cfg.start_perf_monitor, cfg.stop_perf_monitor);
          join_any
          disable fork;
        end: iso_fork join
      end
    end
  endtask : run_phase

  // Monitor SCL to measure the actual frequency of an I2C transaction.
  virtual task automatic perf_monitor(virtual i2c_if vif, ref uvm_event start, ref uvm_event stop);

    `uvm_info(`gfn, "perf_monitor(): Waiting for start event.", UVM_DEBUG)
    start.wait_trigger();
    `uvm_info(`gfn, "perf_monitor(): Got start event.", UVM_DEBUG)

    // Clear out any captured measurements from the previous sample (this limits the size
    // of the queue, and prevents measuring the same period twice)
    cfg.period_q.delete();

    fork begin : iso_fork
      fork
        // Measure the elapsed simulation time between sucessive posedges of SCL. Push each
        // value into the 'period_q[$]' to be consumed elsewhere for checking.
        begin
          realtime last_posedge, current_posedge;
          forever begin
            @(posedge vif.cb.scl_i);
            current_posedge = $realtime;
            if (last_posedge != 0) begin
              cfg.period_q.push_back(time'(current_posedge - last_posedge));
              `uvm_info(`gfn, $sformatf("perf_monitor(): scl_period_observed = %0t",
                                        cfg.period_q[$]), UVM_DEBUG)
            end
            last_posedge = current_posedge;
          end
        end
        // Wait for the trigger event that stops the performance monitor. When this occurs,
        // join and disable the parallel monitoring process.
        begin
          stop.wait_trigger();
          `uvm_info(`gfn, "perf_monitor(): Got stop event.", UVM_DEBUG)
        end
      join_any
      disable fork;
    end : iso_fork join
  endtask

  virtual protected task target_collect_thread();
    i2c_item full_item;
    if (mon_dut_item.stop ||
       (!mon_dut_item.stop && !mon_dut_item.start && !mon_dut_item.rstart)) begin
      cfg.vif.wait_for_host_start(cfg.timing_cfg);
      `uvm_info(`gfn, "Detected START condition.", UVM_HIGH)
    end else begin
      mon_dut_item.rstart = 1'b1;
    end
    mon_dut_item.tran_id = num_dut_tran++;
    mon_dut_item.start = 1'b1;

    target_address_thread();

    if (mon_dut_item.bus_op == BusOpRead) target_read_thread();
    else                                  target_write_thread();

    // send rsp_item to scoreboard
    `downcast(full_item, mon_dut_item.clone());
    full_item.stop = 1'b1;
    if (cfg.vif.rst_ni && full_item.stop && full_item.start) begin
      if (full_item.bus_op == BusOpRead) rd_item_port.write(full_item);
      else                               wr_item_port.write(full_item);
      `uvm_info(`gfn, $sformatf("Sending following full item to scb now:\n%s",
                                full_item.sprint()), UVM_DEBUG)
    end
    mon_dut_item.clear_data();
  endtask: target_collect_thread

  virtual protected task target_address_thread();
    i2c_item clone_item;
    bit rw_req = 1'b0;

    cfg.start_perf_monitor.trigger();

    // sample address and r/w bit
    for (int i = cfg.target_addr_mode - 1; i >= 0; i--) begin
      cfg.vif.get_bit_data("host", cfg.timing_cfg, mon_dut_item.addr[i]);
      `uvm_info(`gfn, $sformatf("target_address_thread() address[%0d] %b",
        i, mon_dut_item.addr[i]), UVM_DEBUG)
    end
    `uvm_info(`gfn, $sformatf("target_address_thread(), address %0x", mon_dut_item.addr), UVM_DEBUG)
    cfg.vif.get_bit_data("host", cfg.timing_cfg, rw_req);
    `uvm_info(`gfn, $sformatf("target_address_thread(): rw %d", rw_req), UVM_DEBUG)

    cfg.stop_perf_monitor.trigger();

    mon_dut_item.bus_op = (rw_req) ? BusOpRead : BusOpWrite;
    // get ack after transmitting address
    mon_dut_item.drv_type = DevAck;
    `downcast(clone_item, mon_dut_item.clone());
    `uvm_info(`gfn, $sformatf("target_address_thread(): Req analysis port"), UVM_DEBUG)
    req_analysis_port.write(clone_item);
    cfg.vif.wait_for_device_ack_or_nack(cfg.timing_cfg, mon_dut_item.addr_ack);
    if (mon_dut_item.addr_ack == 1'b1) cfg.got_nack.trigger();
    `uvm_info(`gfn,
              $sformatf("target_address_thread(): %0s", mon_dut_item.addr_ack ? "ACK": "NACK"),
      UVM_DEBUG)
    `uvm_info(`gfn, "target_address_thread() detected ACK", UVM_FULL)
  endtask : target_address_thread

  virtual protected task target_read_thread();
    i2c_item clone_item;

    mon_dut_item.stop   = 1'b0;
    mon_dut_item.rstart = 1'b0;
    mon_dut_item.ack    = 1'b0;
    mon_dut_item.nack   = 1'b0;
    while (!mon_dut_item.stop && !mon_dut_item.rstart) begin
      // ask driver response read data
      mon_dut_item.drv_type = RdData;
      `downcast(clone_item, mon_dut_item.clone());
      `uvm_info(`gfn, "Req analysis port: read thread", UVM_HIGH)
      req_analysis_port.write(clone_item);

      cfg.start_perf_monitor.trigger();

      // sample read data
      for (int i = 7; i >= 0; i--) begin
        cfg.vif.get_bit_data("device", cfg.timing_cfg, mon_data[i]);
        `uvm_info(`gfn, $sformatf("target_read_thread() trans %0d, byte %0d, bit[%0d] %0b",
            mon_dut_item.tran_id, mon_dut_item.num_data+1, i, mon_data[i]), UVM_DEBUG)
      end

      cfg.stop_perf_monitor.trigger();

      mon_dut_item.data_q.push_back(mon_data);
      mon_dut_item.num_data++;
      `uvm_info(`gfn, $sformatf("target_read_thread() trans %0d, byte %0d 0x%0x",
          mon_dut_item.tran_id, mon_dut_item.num_data, mon_data), UVM_HIGH)
      // sample host ack/nack (in the last byte, nack can be issue if rcont is set)
      cfg.vif.wait_for_host_ack_or_nack(cfg.timing_cfg, mon_dut_item.ack, mon_dut_item.nack);
      if (mon_dut_item.nack) cfg.got_nack.trigger();
      mon_dut_item.data_ack_q.push_back(mon_dut_item.ack && !mon_dut_item.nack);
      `uvm_info(`gfn, $sformatf("target_read_thread() saw %0s",
          (mon_dut_item.ack) ? "ACK" : "NACK"), UVM_HIGH)
      // if nack is issued, next bit must be stop or rstart
      if (mon_dut_item.nack) begin
        cfg.vif.wait_for_host_stop_or_rstart(cfg.timing_cfg,
                                             mon_dut_item.rstart,
                                             mon_dut_item.stop);
        `uvm_info(`gfn, $sformatf("target_read_thread() detected %0s",
          (mon_dut_item.stop) ? "STOP" : "RSTART"), UVM_FULL)
      end
    end
  endtask : target_read_thread

  virtual protected task target_write_thread();
    i2c_item clone_item;

    mon_dut_item.stop   = 1'b0;
    mon_dut_item.rstart = 1'b0;
    `uvm_info(`gfn, $sformatf("target_write_thread() begin: tran_id:%0d num_data%0d",
                              mon_dut_item.tran_id, mon_dut_item.num_data), UVM_FULL)

    while (!mon_dut_item.stop && !mon_dut_item.rstart) begin
      fork
        begin : iso_fork_write
          fork
            begin
              bit ack_nack;

              cfg.start_perf_monitor.trigger();

              for (int i = 7; i >= 0; i--) begin
                cfg.vif.get_bit_data("host", cfg.timing_cfg, mon_data[i]);
              end

              cfg.stop_perf_monitor.trigger();

              `uvm_info(`gfn, $sformatf("target_write_thread() collected data %0x",
                mon_data), UVM_DEBUG)
              mon_dut_item.num_data++;
              mon_dut_item.data_q.push_back(mon_data);
              `uvm_info(`gfn, $sformatf("target_write_thread() data %2x num_data:%0d",
                                        mon_data, mon_dut_item.num_data), UVM_HIGH)
              // send device ack to host write
              mon_dut_item.wdata = mon_data;
              mon_dut_item.drv_type = DevAck;
              `downcast(clone_item, mon_dut_item.clone());
              `uvm_info(`gfn, $sformatf("target_write_thread() Req analysis port ACK."), UVM_DEBUG)
              req_analysis_port.write(clone_item);
              // sample ack/nack
              cfg.vif.wait_for_device_ack_or_nack(cfg.timing_cfg, ack_nack);
              if (ack_nack == 1'b1) cfg.got_nack.trigger();
              mon_dut_item.data_ack_q.push_back(ack_nack);
            end
            begin
              cfg.vif.wait_for_host_stop_or_rstart(cfg.timing_cfg,
                                                   mon_dut_item.rstart,
                                                   mon_dut_item.stop);
              `uvm_info(`gfn, $sformatf("target_write_thread() detected %0s %0b",
                (mon_dut_item.stop) ? "STOP" : "RSTART", mon_dut_item.stop), UVM_FULL)
            end
          join_any
          disable fork;
        end : iso_fork_write
      join
    end
    `uvm_info(`gfn, $sformatf("target_write_thread() end: tran_id:%0d num_data:%0d",
                              mon_dut_item.tran_id, mon_dut_item.num_data), UVM_FULL)
  endtask : target_write_thread

  // update of_to_end to prevent sim finished when there is any activity on the bus
  // ok_to_end = 0 (bus busy) / 1 (bus idle)
  virtual task monitor_ready_to_end();
    if (cfg.if_mode == Host) begin
      int scl_cnt = 0;
      if (cfg.en_monitor) begin
        ok_to_end = 0;
      end
      forever begin
        @(cfg.vif.cb);
        if (cfg.vif.scl_i) scl_cnt++;
        else scl_cnt = 0;
        if (scl_cnt > 100) ok_to_end = 1;
      end
    end else begin
      forever begin
        @(cfg.vif.scl_i or cfg.vif.sda_i or cfg.vif.scl_o or cfg.vif.sda_o);
        ok_to_end = (cfg.vif.scl_i == 1'b1) && (cfg.vif.sda_i == 1'b1);
      end
    end
  endtask : monitor_ready_to_end

  // Handle an externally-triggered monitor reset
  // This routine is currently triggered externally by setting cfg.monitor_rst = 1 in the
  // hrst_vseq. This is a hack to try and keep the dv env in sync with stimulus that
  // short-circuits the current transaction with an early RSTART/STOP. It should be refactored
  // and removed, preferably with proper modelling inside the scoreboard/refmodel.
  //
  // - Wait for the next edge on the bus
  // - Clear temporary state about the currently monitored transaction
  // - Set stop bit to indicate completion of the current transaction
  task handle_rst(input string task_name);
    int wait_timeout_ns = 1_000_000; // 1 ms
    `uvm_info(`gfn, $sformatf("handle_rst() from task '%0s'", task_name), UVM_MEDIUM)

    // Wait for the next bus activity via the clocking block
    @(cfg.vif.cb);

    // Clear the temporary item used to accumulate in-progress transactions
    mon_dut_item.clear_all();

    // Wait for cfg.monitor_rst to de-assert (within 1ms).
    `DV_WAIT(// WAIT_COND_
             (!cfg.monitor_rst),
             // MSG_
             ,
             // TIMEOUT_NS_
             wait_timeout_ns,
             // ID_
             $sformatf("handle_rst: reset failed to de-asserted from task '%0s'", task_name));

    // Indicate the end of the current transaction with a stop condition.
    cfg.got_stop = 1;
  endtask


  virtual protected task controller_collect_thread();
    i2c_item full_item;
    bit skip_the_loop = 0;

    // Wait for the vseq to clear this at the start of the next stimulus round.
    wait(cfg.got_stop == 0);

    cfg.valid_addr = 0;
    if (mon_dut_item.stop ||
        (!mon_dut_item.stop && !mon_dut_item.start && !mon_dut_item.rstart)) begin
      cfg.vif.wait_for_host_start(cfg.timing_cfg);
      `uvm_info(`gfn, "Detected START", UVM_MEDIUM)
    end else begin
      mon_dut_item.rstart = 1'b1;
    end
    mon_dut_item.tran_id = num_dut_tran++;
    mon_dut_item.start = 1'b1;

    controller_address_thread(skip_the_loop);
    if (skip_the_loop) begin
      `uvm_info(`gfn, "Skipping the loop now.", UVM_MEDIUM)
      return;
    end

    if (mon_dut_item.bus_op == BusOpRead) controller_read_thread();
    else                                  controller_write_thread();

    // Send completed rsp_item to scoreboard
    `downcast(full_item, mon_dut_item.clone());
    full_item.stop = 1'b1;
    if (mon_dut_item.bus_op == BusOpRead) begin
      full_item.read = 1;
      analysis_port.write(full_item);
    end
    mon_dut_item.clear_data();

  endtask: controller_collect_thread


  task controller_address_thread(ref bit skip);
    bit r_bit = 1'b0;
    bit do_skip = 0; // ref variable update is not supported in fork-join_any/none
    skip = 0;

    fork begin : iso_fork
      fork
        begin // address capture thread
          // collecting address
          for (int i = cfg.target_addr_mode - 1; i >= 0; i--) begin
            cfg.vif.p_edge_scl();
            mon_dut_item.addr[i] = cfg.vif.cb.sda_i;
            `uvm_info(`gfn, $sformatf("controller_address_thread() address[%0d] %b",
                                      i, mon_dut_item.addr[i]), UVM_DEBUG)
          end
          `uvm_info(`gfn, $sformatf("controller_address_thread() address %0x",
                                    mon_dut_item.addr), UVM_MEDIUM)

          cfg.vif.p_edge_scl();
          r_bit = cfg.vif.cb.sda_i;
          `uvm_info(`gfn, $sformatf("controller_address_thread() rw %d", r_bit), UVM_MEDIUM)

          mon_dut_item.bus_op = (r_bit) ? BusOpRead : BusOpWrite;
          cfg.valid_addr = is_target_addr(mon_dut_item.addr);
          cfg.is_read = r_bit;

          if (mon_dut_item.bus_op == BusOpRead) begin
            cfg.read_addr_q.push_back(cfg.valid_addr);
          end
          `uvm_info(`gfn, $sformatf("allow_bad_addr: %0d valid_addr:%0d",
                                    cfg.allow_bad_addr, cfg.valid_addr), UVM_MEDIUM)

          if (cfg.allow_bad_addr & !cfg.valid_addr) begin

            // skip rest of transaction and wait for next start
            `uvm_info(`gfn, $sformatf("illegal address :0x%x", mon_dut_item.addr), UVM_MEDIUM)
            mon_dut_item.clear_all();
            do_skip = 1;

          end else begin
            bit acknack_bit;

            // Get ACK/NACK bit
            cfg.vif.p_edge_scl();
            acknack_bit = cfg.vif.cb.sda_i;
            `uvm_info(`gfn, $sformatf("controller_address_thread() saw %0s",
                                      (!acknack_bit) ? "ACK" : "NACK"), UVM_MEDIUM)
            if (acknack_bit) cfg.got_nack.trigger();

          end
        end
        begin
          begin
            wait(cfg.monitor_rst);
            handle_rst("controller_address_thread()");
          end
          do_skip = 1; // Skip processing rest of the transaction
        end
      join_any
      disable fork;
    end : iso_fork join
    skip = do_skip;
  endtask: controller_address_thread


  // Rewrite read / write task using glitch free edge functions.
  task controller_read_thread();
    mon_dut_item.stop   = 1'b0;
    mon_dut_item.rstart = 1'b0;
    mon_dut_item.ack    = 1'b0;
    mon_dut_item.nack   = 1'b0;
    mon_rstart = 0;
    target_read_phase = 1;
    // Previous data collecting thread replied on nack / stop
    // For ack / stop test, this thread need to be forked with
    // separate ack_stop_monitor

    fork begin
      fork
        // This data collecting thread is closed upon setting mon_rstart
        // mon_rstart, when ack_stop_mon() task detects ack / stop event
        while (!mon_dut_item.stop && !mon_dut_item.rstart) begin
          // ask driver response read data
          mon_dut_item.drv_type = RdData;
          for (int i = 7; i >= 0; i--) begin
            cfg.vif.sample_target_data(cfg.timing_cfg, mon_data[i]);
            `uvm_info(`gfn,
              $sformatf("controller_read_thread(), trans %0d, byte %0d, bit[%0d] %0b",
              mon_dut_item.tran_id, mon_dut_item.num_data+1, i, mon_data[i]), UVM_HIGH)
          end
          cfg.vif.wait_for_host_ack_or_nack(cfg.timing_cfg, mon_dut_item.ack, mon_dut_item.nack);
          if (mon_dut_item.nack) cfg.got_nack.trigger();
          `uvm_info(`gfn, $sformatf("controller_read_thread(), detected %0s",
                                    (mon_dut_item.ack) ? "ACK" : "NACK"), UVM_MEDIUM)

          cfg.rcvd_rd_byte++;
          // Hold data push until send ack / nack
          mon_dut_item.data_q.push_back(mon_data);
          mon_dut_item.num_data++;
          `uvm_info(`gfn, $sformatf("controller_read_thread(), trans %0d, byte %0d 0x%0x",
                    mon_dut_item.tran_id, mon_dut_item.num_data, mon_data), UVM_MEDIUM)

          // if nack is issued, next bit must be stop or rstart
          if (mon_dut_item.nack) begin
            cfg.vif.wait_for_host_stop_or_rstart(cfg.timing_cfg,
                                                 mon_dut_item.rstart,
                                                 mon_dut_item.stop);
            `uvm_info(`gfn, $sformatf("controller_read_thread(), detected %0s",
                                      (mon_dut_item.stop) ? "STOP" : "RSTART"), UVM_MEDIUM)
            if (mon_dut_item.stop) cfg.got_stop = 1;
          end
        end
        begin
          // This is undeterministic event so cannot set the timeout,
          // but this thread will be terminated by the other thread.
          wait((cfg.allow_ack_stop & mon_rstart) | cfg.monitor_rst);
          handle_rst("controller_read_thread()");
        end
      join_any
      disable fork;
    end join
    target_read_phase = 0;

    `uvm_info(`gfn, $sformatf("controller_read_thread() end stop:%0d rs:%0d",
                              mon_dut_item.stop, mon_dut_item.rstart), UVM_HIGH)
  endtask: controller_read_thread

  task controller_write_thread();
    mon_dut_item.stop   = 1'b0;
    mon_dut_item.rstart = 1'b0;
    fork begin: iso_fork
      fork
        forever begin : collect_write_data

          begin : get_write_bits
            bit [7:0] data;
            for (int i = 7; i >= 0; i--) begin
              cfg.vif.p_edge_scl();
              data[i] = cfg.vif.sda_i;
            end
            `uvm_info(`gfn, $sformatf("controller_write_thread() got data 0x%2x",
              data), UVM_HIGH)
          end

          begin : get_ack_nack_bit
            bit acknack_bit;
            `uvm_info(`gfn, "controller_write_thread() waiting for N(ACK)...", UVM_MEDIUM)
            cfg.vif.p_edge_scl();
            acknack_bit = cfg.vif.cb.sda_i;
            `uvm_info(`gfn, $sformatf("controller_write_thread() saw %0s",
                                      (!acknack_bit) ? "ACK" : "NACK"), UVM_MEDIUM)
            if (acknack_bit) cfg.got_nack.trigger();
          end

          // If the target NACKs a controller write byte, the controller should
          // immediately send a stop or rstart condition, ending the transfer.
          // However, a P/Sr condition at any point is valid to end the transfer. The
          // 'end_of_transfer_thread' below will terminate this fork-join block for both
          // of these cases.
        end
        begin
          wait(cfg.monitor_rst);
          handle_rst("controller_write_thread");
        end
        begin: end_of_transfer_thread
          // STOP / RSTART can occur at any time, ending the transfer. Await those here.
          cfg.vif.wait_for_host_stop_or_rstart(
            cfg.timing_cfg, mon_dut_item.rstart, mon_dut_item.stop);
          `uvm_info(`gfn, $sformatf("controller_write_thread() saw %0s",
                                    (mon_dut_item.stop) ? "STOP" : "RSTART"), UVM_MEDIUM)
          if (mon_dut_item.stop) cfg.got_stop = 1;
        end
      join_any
      disable fork;
    end: iso_fork join
  endtask: controller_write_thread

  task ack_stop_mon();
    bit stop, rstart;
    forever begin
      @(cfg.vif.cb);
      if (target_read_phase) begin
        cfg.vif.wait_for_host_stop_or_rstart(cfg.timing_cfg, rstart, stop);
        if ((rstart | stop) & mon_dut_item.ack) begin
          if (cfg.allow_ack_stop) begin
            `uvm_info("ack_stop_mon",
                      $sformatf("detect ack_stop %2b (rs,p)", {rstart, stop}), UVM_MEDIUM)
            mon_rstart = 1;
            if (stop) cfg.ack_stop_det = 1;
          end else begin
            `uvm_error(`gfn, "ack_stop detected")
          end
          mon_dut_item.rstart = rstart;
          mon_dut_item.stop = stop;
          if (stop) cfg.got_stop = 1;
          rstart = 0;
          stop = 0;
        end
      end
    end
  endtask

  function bit is_target_addr(bit [6:0] addr);
    return (addr == cfg.target_addr0 || addr == cfg.target_addr1);
  endfunction
endclass : i2c_monitor
