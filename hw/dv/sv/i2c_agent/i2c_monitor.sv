// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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
    wait(cfg.vif.rst_ni);
    if (cfg.if_mode == Host) begin
      i2c_item full_item;
      bit skip_the_loop;
      fork
        forever begin
          wait(cfg.en_monitor);
          cfg.valid_addr = 0;
          skip_the_loop = 0;
          cfg.vif.drv_phase = DrvIdle;
          if (mon_dut_item.stop ||
              (!mon_dut_item.stop && !mon_dut_item.start && !mon_dut_item.rstart)) begin
            cfg.vif.wait_for_host_start(cfg.timing_cfg);
            `uvm_info(`gfn, "\nmonitor, detect HOST START", UVM_MEDIUM)
          end else begin
            mon_dut_item.rstart = 1'b1;
          end
          mon_dut_item.tran_id = num_dut_tran;
          mon_dut_item.start = 1'b1;
          target_addr(skip_the_loop);
          if (skip_the_loop) continue;
          if (mon_dut_item.bus_op == BusOpRead) target_read();
          else target_write();

          // send rsp_item to scoreboard
          `downcast(full_item, mon_dut_item.clone());
          full_item.stop = 1'b1;
          if (mon_dut_item.bus_op == BusOpRead) begin
            full_item.read = 1;
            analysis_port.write(full_item);
          end
          num_dut_tran++;
          mon_dut_item.clear_data();
        end // forever begin
        ack_stop_mon();
      join_none
    end else begin
      forever begin
        fork
          begin: iso_fork
            fork
              begin
                collect_thread(phase);
              end
              begin // if (on-the-fly) reset is monitored, drop the item
                wait_for_reset_and_drop_item();
                `uvm_info(`gfn, $sformatf("\nmonitor is reset, drop item\n%s",
                                          mon_dut_item.sprint()), UVM_DEBUG)
              end
            join_any
            disable fork;
          end: iso_fork
        join
      end
    end
  endtask : run_phase

  // Collect transactions forever
  virtual protected task collect_thread(uvm_phase phase);
    i2c_item full_item;
    wait(cfg.en_monitor);
    if (mon_dut_item.stop ||
       (!mon_dut_item.stop && !mon_dut_item.start && !mon_dut_item.rstart)) begin
      cfg.vif.wait_for_host_start(cfg.timing_cfg);
      `uvm_info(`gfn, "\nmonitor, detect HOST START", UVM_HIGH)
    end else begin
      mon_dut_item.rstart = 1'b1;
    end
    num_dut_tran++;
    mon_dut_item.start = 1'b1;
    // monitor address for non-chained reads
    address_thread();
    // monitor read/write data
    if (mon_dut_item.bus_op == BusOpRead) read_thread();
    else                                  write_thread();
    // send rsp_item to scoreboard
    `downcast(full_item, mon_dut_item.clone());
    full_item.stop = 1'b1;
    if (cfg.vif.rst_ni && full_item.stop && full_item.start) begin
      if (full_item.bus_op == BusOpRead) rd_item_port.write(full_item);
      else                               wr_item_port.write(full_item);
      `uvm_info(`gfn, $sformatf("\nmonitor, send full item to scb\n%s",
          full_item.sprint()), UVM_DEBUG)
    end
    mon_dut_item.clear_data();
  endtask: collect_thread

  virtual protected task address_thread();
    i2c_item clone_item;
    bit rw_req = 1'b0;

    // sample address and r/w bit
    mon_dut_item.tran_id = num_dut_tran;
    for (int i = cfg.target_addr_mode - 1; i >= 0; i--) begin
      cfg.vif.get_bit_data("host", cfg.timing_cfg, mon_dut_item.addr[i]);
      `uvm_info(`gfn, $sformatf("\nmonitor, address[%0d] %b", i, mon_dut_item.addr[i]), UVM_HIGH)
    end
    `uvm_info(`gfn, $sformatf("\nmonitor, address %0x", mon_dut_item.addr), UVM_HIGH)
    cfg.vif.get_bit_data("host", cfg.timing_cfg, rw_req);
    `uvm_info(`gfn, $sformatf("\nmonitor, rw %d", rw_req), UVM_HIGH)
    mon_dut_item.bus_op = (rw_req) ? BusOpRead : BusOpWrite;
    // get ack after transmitting address
    mon_dut_item.drv_type = DevAck;
    `downcast(clone_item, mon_dut_item.clone());
    `uvm_info(`gfn, $sformatf("Req analysis port: address thread"), UVM_HIGH)
    req_analysis_port.write(clone_item);
    cfg.vif.wait_for_device_ack_or_nack(cfg.timing_cfg, mon_dut_item.addr_ack);
    `uvm_info(`gfn,
      $sformatf("\nmonitor, address : %s", mon_dut_item.addr_ack ? "ACK": "NACK"),
      UVM_DEBUG)
    `uvm_info(`gfn, "\nmonitor, address, detect TARGET ACK", UVM_HIGH)
  endtask : address_thread

  virtual protected task read_thread();
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
      // sample read data
      for (int i = 7; i >= 0; i--) begin
        cfg.vif.get_bit_data("device", cfg.timing_cfg, mon_data[i]);
        `uvm_info(`gfn, $sformatf("\nmonitor, rd_data, trans %0d, byte %0d, bit[%0d] %0b",
            mon_dut_item.tran_id, mon_dut_item.num_data+1, i, mon_data[i]), UVM_HIGH)
      end
      mon_dut_item.data_q.push_back(mon_data);
      mon_dut_item.num_data++;
      `uvm_info(`gfn, $sformatf("\nmonitor, rd_data, trans %0d, byte %0d 0x%0x",
          mon_dut_item.tran_id, mon_dut_item.num_data, mon_data), UVM_HIGH)
      // sample host ack/nack (in the last byte, nack can be issue if rcont is set)
      cfg.vif.wait_for_host_ack_or_nack(cfg.timing_cfg, mon_dut_item.ack, mon_dut_item.nack);
      mon_dut_item.data_ack_q.push_back(mon_dut_item.ack && !mon_dut_item.nack);
      `DV_CHECK_NE_FATAL({mon_dut_item.ack, mon_dut_item.nack}, 2'b11)
      `uvm_info(`gfn, $sformatf("\nmonitor, detect HOST %s",
          (mon_dut_item.ack) ? "ACK" : "NO_ACK"), UVM_HIGH)
      // if nack is issued, next bit must be stop or rstart
      if (mon_dut_item.nack) begin
        cfg.vif.wait_for_host_stop_or_rstart(cfg.timing_cfg,
                                             mon_dut_item.rstart,
                                             mon_dut_item.stop);
        `DV_CHECK_NE_FATAL({mon_dut_item.rstart, mon_dut_item.stop}, 2'b11)
        `uvm_info(`gfn, $sformatf("\nmonitor, rd_data, detect HOST %s",
            (mon_dut_item.stop) ? "STOP" : "RSTART"), UVM_HIGH)
      end
    end
  endtask : read_thread

  virtual protected task write_thread();
    i2c_item clone_item;

    mon_dut_item.stop   = 1'b0;
    mon_dut_item.rstart = 1'b0;
    `uvm_info(`gfn, $sformatf("host_write_thread begin: tran_id:%0d num_data%0d",
                              mon_dut_item.tran_id, mon_dut_item.num_data), UVM_HIGH)

    while (!mon_dut_item.stop && !mon_dut_item.rstart) begin
      fork
        begin : iso_fork_write
          fork
            begin
              bit ack_nack;
               `uvm_info(`gfn, "Req analysis port: write thread data", UVM_HIGH)
              // ask driver's response a write request
              mon_dut_item.drv_type = WrData;
              `downcast(clone_item, mon_dut_item.clone());
              req_analysis_port.write(clone_item);
              for (int i = 7; i >= 0; i--) begin
                cfg.vif.get_bit_data("host", cfg.timing_cfg, mon_data[i]);
              end
              `uvm_info(`gfn, $sformatf("Monitor collected data %0x", mon_data), UVM_HIGH)
              mon_dut_item.num_data++;
              mon_dut_item.data_q.push_back(mon_data);
              `uvm_info(`gfn, $sformatf("host_write_thread data %2x num_data:%0d",
                                        mon_data, mon_dut_item.num_data), UVM_HIGH)
              // send device ack to host write
              mon_dut_item.wdata = mon_data;
              mon_dut_item.drv_type = DevAck;
              `downcast(clone_item, mon_dut_item.clone());
              `uvm_info(`gfn, $sformatf("Req analysis port: write thread ack"), UVM_HIGH)
              req_analysis_port.write(clone_item);
              // sample ack/nack
              cfg.vif.wait_for_device_ack_or_nack(cfg.timing_cfg, ack_nack);
              mon_dut_item.data_ack_q.push_back(ack_nack);
            end
            begin
              cfg.vif.wait_for_host_stop_or_rstart(cfg.timing_cfg,
                                                   mon_dut_item.rstart,
                                                   mon_dut_item.stop);
              `DV_CHECK_NE_FATAL({mon_dut_item.rstart, mon_dut_item.stop}, 2'b11)
              `uvm_info(`gfn, $sformatf("\nmonitor, wr_data, detect HOST %s %0b",
                  (mon_dut_item.stop) ? "STOP" : "RSTART", mon_dut_item.stop), UVM_HIGH)
            end
          join_any
          disable fork;
        end : iso_fork_write
      join
    end
    `uvm_info(`gfn, $sformatf("host_write_thread end: tran_id:%0d num_data:%0d",
                              mon_dut_item.tran_id, mon_dut_item.num_data), UVM_HIGH)
  endtask : write_thread

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

  // Handle agent reset and set stop bit to indicate completion of the current transaction
  task handle_monitor_rst(input string task_name);
    int wait_timeout_ns = 1_000_000; // 1 ms
    if (cfg.monitor_rst) begin
      @(cfg.vif.cb);
      mon_dut_item.clear_all();
      `DV_WAIT((!cfg.monitor_rst), , wait_timeout_ns, $sformatf("%s:monitor reset de-assert",
               task_name));
      cfg.got_stop = 1;
      `uvm_info(`gfn, $sformatf("monitor forceout from %s", task_name), UVM_MEDIUM)
    end
  endtask

  task target_addr(ref bit skip);
    bit r_bit = 1'b0;
    bit do_skip = 0; // ref variable update is not supported in fork-join_any/none
    skip = 0;
    fork begin
       fork
         begin // address capture thread
           cfg.vif.drv_phase = DrvAddr;
           // collecting address
           for (int i = cfg.target_addr_mode - 1; i >= 0; i--) begin
             cfg.vif.p_edge_scl();
             mon_dut_item.addr[i] = cfg.vif.cb.sda_i;
             `uvm_info(`gfn, $sformatf("\nmonitor, address[%0d] %b", i, mon_dut_item.addr[i]),
                       UVM_HIGH)
           end
           `uvm_info(`gfn, $sformatf("\nmonitor, address %0x", mon_dut_item.addr), UVM_MEDIUM)
           cfg.vif.p_edge_scl();
           r_bit = cfg.vif.cb.sda_i;
           `uvm_info(`gfn, $sformatf("\nmonitor, rw %d", r_bit), UVM_MEDIUM)
           mon_dut_item.bus_op = (r_bit) ? BusOpRead : BusOpWrite;
           cfg.valid_addr = is_target_addr(mon_dut_item.addr);
           cfg.is_read = r_bit;

           if (mon_dut_item.bus_op == BusOpRead) begin
             cfg.read_addr_q.push_back(cfg.valid_addr);
           end
           `uvm_info(`gfn, $sformatf("allow_bad_addr : %0d is_target_addr:%0d",
                                     cfg.allow_bad_addr, cfg.valid_addr), UVM_MEDIUM)
           if (cfg.allow_bad_addr & !cfg.valid_addr) begin
             // skip rest of transaction and wait for next start
             `uvm_info(`gfn, $sformatf("illegal address :0x%x", mon_dut_item.addr), UVM_MEDIUM)
             mon_dut_item.clear_all();
             do_skip = 1;
           end else begin
             // expect target addr ack
             cfg.vif.sample_target_data(cfg.timing_cfg, r_bit);
             `DV_CHECK_CASE_EQ(r_bit, 1'b0)
           end
         end
         begin // agent reset thread
           bit rst_detected = 0;
           wait(cfg.monitor_rst);
           handle_monitor_rst("target_addr");
           do_skip = 1; // Skip processing rest of the transaction
         end
       join_any
       disable fork;
      end
    join
    skip = do_skip;
  endtask

  // Rewrite read / write task using glitch free edge functions.
  task target_read();
    mon_dut_item.stop   = 1'b0;
    mon_dut_item.rstart = 1'b0;
    mon_dut_item.ack    = 1'b0;
    mon_dut_item.nack   = 1'b0;
    mon_rstart = 0;
    target_read_phase = 1;
    // Previous data collecting thread replied on nack / stop
    // For ack / stop test, this thread need to be forked with
    // separate ack_stop_monitor
    cfg.vif.drv_phase = DrvRd;

    fork begin
      fork
        // This data collecting thread is closed upon setting mon_rstart
        // mon_rstart, when ack_stop_mon task detect ack / stop event
        while (!mon_dut_item.stop && !mon_dut_item.rstart) begin
          // ask driver response read data
          mon_dut_item.drv_type = RdData;
          for (int i = 7; i >= 0; i--) begin
            cfg.vif.sample_target_data(cfg.timing_cfg, mon_data[i]);
            `uvm_info(`gfn, $sformatf("\nmonitor, target_read, trans %0d, byte %0d, bit[%0d] %0b",
                      mon_dut_item.tran_id, mon_dut_item.num_data+1, i, mon_data[i]), UVM_HIGH)
          end
          cfg.vif.wait_for_host_ack_or_nack(cfg.timing_cfg, mon_dut_item.ack, mon_dut_item.nack);
          `DV_CHECK_NE_FATAL({mon_dut_item.ack, mon_dut_item.nack}, 2'b11)
          `uvm_info(`gfn, $sformatf("\nmonitor, target_read detect HOST %s",
                                    (mon_dut_item.ack) ? "ACK" : "NO_ACK"), UVM_MEDIUM)

          cfg.rcvd_rd_byte++;
          // Hold data push until send ack / nack
          mon_dut_item.data_q.push_back(mon_data);
          mon_dut_item.num_data++;
          `uvm_info(`gfn, $sformatf("\nmonitor, target_read, trans %0d, byte %0d 0x%0x",
                    mon_dut_item.tran_id, mon_dut_item.num_data, mon_data), UVM_MEDIUM)

          // if nack is issued, next bit must be stop or rstart
          if (mon_dut_item.nack) begin
            cfg.vif.wait_for_host_stop_or_rstart(cfg.timing_cfg,
                                                 mon_dut_item.rstart,
                                                 mon_dut_item.stop);
            `DV_CHECK_NE_FATAL({mon_dut_item.rstart, mon_dut_item.stop}, 2'b11)
            `uvm_info(`gfn, $sformatf("\nmonitor, target_read, detect HOST %s",
                                      (mon_dut_item.stop) ? "STOP" : "RSTART"), UVM_MEDIUM)
            if (mon_dut_item.stop) cfg.got_stop = 1;
          end
        end
        begin
          // This is undeterministic event so cannot set the timeout,
          // but this thread will be terminated by the other thread.
          wait((cfg.allow_ack_stop & mon_rstart) | cfg.monitor_rst);
          handle_monitor_rst("target_read");
        end
      join_any
      disable fork;
    end join
    target_read_phase = 0;

    `uvm_info(`gfn, $sformatf("target_read end stop:%0d rs:%0d",
                              mon_dut_item.stop, mon_dut_item.rstart), UVM_HIGH)
  endtask

  task target_write();
    bit r_bit;
    mon_dut_item.stop   = 1'b0;
    mon_dut_item.rstart = 1'b0;
    cfg.vif.drv_phase = DrvWr;
    fork begin
      fork
        while (!mon_dut_item.stop && !mon_dut_item.rstart) begin
          mon_dut_item.drv_type = WrData;
          for (int i = 7; i >= 0; i--) begin
            cfg.vif.p_edge_scl();
          end
          // check for ack
          cfg.vif.p_edge_scl();
          r_bit = cfg.vif.cb.sda_i;
          `uvm_info(`gfn, $sformatf("\nmonitor, target_write detect HOST %s",
                                   (!r_bit) ? "ACK" : "NO_ACK"), UVM_MEDIUM)
          // if nack is issued, next bit must be stop or rstart

          if (!r_bit) begin
            cfg.vif.wait_for_host_stop_or_rstart(cfg.timing_cfg,
                                                 mon_dut_item.rstart,
                                                 mon_dut_item.stop);
            `DV_CHECK_NE_FATAL({mon_dut_item.rstart, mon_dut_item.stop}, 2'b11)
            `uvm_info(`gfn, $sformatf("\nmonitor, target_write detect HOST %s",
                                      (mon_dut_item.stop) ? "STOP" : "RSTART"), UVM_MEDIUM)
            if (mon_dut_item.stop) cfg.got_stop = 1;
          end
        end
        begin
          wait(cfg.monitor_rst);
          handle_monitor_rst("target_write");
        end
      join_any
      disable fork;
    end join
  endtask // target_write

  task ack_stop_mon();
    bit stop, rstart;
    forever begin
      @(cfg.vif.cb);
      if (target_read_phase) begin
        cfg.vif.wait_for_host_stop_or_rstart(cfg.timing_cfg, rstart, stop);
        `DV_CHECK_NE_FATAL({rstart, stop}, 2'b11)
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
