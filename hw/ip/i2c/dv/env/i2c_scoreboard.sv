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
  local i2c_item  rd_pending_item;
  local i2c_item  rd_pending_q[$];
  local i2c_item  exp_rd_q[$];
  local i2c_item  exp_wr_q[$];
  local uint      rd_wait;

  local bit       host_init = 1'b0;
  local uint      rdata_cnt = 0;
  local uint      tran_id = 0;
  local uint      num_exp_tran = 0;

  // use seperate fifos for dut_rd and dut_wr item
  uvm_tlm_analysis_fifo #(i2c_item) rd_item_fifo;
  uvm_tlm_analysis_fifo #(i2c_item) wr_item_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    rd_item_fifo = new("rd_item_fifo", this);
    wr_item_fifo = new("wr_item_fifo", this);
    rd_pending_item = new("rd_pending_item" );
    exp_rd_item = new("exp_rd_item");
    exp_wr_item = new("exp_wr_item");
  endfunction : build_phase

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      compare_trans(BusOpWrite);
      compare_trans(BusOpRead);
    join
  endtask : run_phase

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg   csr;
    i2c_item  sb_exp_wr_item;
    i2c_item  sb_exp_rd_item;
    bit do_read_check = 1'b0;
    bit write = item.is_write();

    uvm_reg_addr_t csr_addr = get_normalized_addr(item.a_addr);
    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("access unexpected addr 0x%0h", csr_addr))
    end

    sb_exp_wr_item = new();
    sb_exp_rd_item = new();
    if (write && channel == AddrChannel) begin
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

          if (host_init) begin
            fbyte = get_field_val(ral.fdata.fbyte, item.a_data);
            start = bit'(get_field_val(ral.fdata.start, item.a_data));
            stop  = bit'(get_field_val(ral.fdata.stop, item.a_data));
            read  = bit'(get_field_val(ral.fdata.read, item.a_data));
            rcont = bit'(get_field_val(ral.fdata.rcont, item.a_data));
            nakok = bit'(get_field_val(ral.fdata.nakok, item.a_data));

            // transaction is being started/rstarted, target address is programmed
            if (start) begin
              tran_id++;
              if (exp_wr_item.start && !sb_exp_wr_item.stop &&
                  exp_wr_item.bus_op == BusOpWrite) begin
                // this is a write end with rstart, write to sb_wr_fifo
                exp_wr_item.rstart = 1'b1;
                `downcast(sb_exp_wr_item, exp_wr_item.clone());
                sb_exp_wr_item.stop = 1'b1;
                exp_wr_item.clear_all();
              end
              `DV_CHECK_EQ(read, 1'b0)
              `DV_CHECK_EQ(stop, 1'b0)
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
            end else begin // transaction has been started/rstarted
              // write transaction
              if (exp_wr_item.start && exp_wr_item.bus_op == BusOpWrite) begin
                exp_wr_item.data_q.push_back(fbyte);
                exp_wr_item.num_data++;
                exp_wr_item.stop = stop;
                if (exp_wr_item.stop) begin
                  // this is a write end with stop, write to the sb_wr_fifo
                  `downcast(sb_exp_wr_item, exp_wr_item.clone());
                  exp_wr_item.clear_all();
                end
              end
              // read transaction
              if (exp_rd_item.start && exp_rd_item.bus_op == BusOpRead) begin
                if (read) begin  // read flag
                  i2c_item tmp_rd_item;

                  // get the number of byte to read, fmt_read flag is set
                  exp_rd_item.num_data = (fbyte == 8'd0) ? 256 : fbyte;
                  exp_rd_item.stop  = stop;
                  `DV_CHECK_EQ(read, 1'b1)
                  exp_rd_item.read   = read;
                  exp_rd_item.rcont  = rcont;
                  exp_rd_item.nakok  = nakok;
                  exp_rd_item.nack   = ~exp_rd_item.rcont;
                  exp_rd_item.rstart = (exp_rd_item.stop) ? 1'b0 : 1'b1;
                  //push into temporal rd_pending_q (data still empty)
                  `downcast(tmp_rd_item, exp_rd_item.clone());
                  rd_pending_q.push_back(tmp_rd_item);
                  exp_rd_item.start = 0;
                  exp_rd_item.clear_data();
                end
              end
            end
          end
        end
      endcase

      // push sb_exp_wr_item into exp_fifo
      if (host_init && sb_exp_wr_item.start && sb_exp_wr_item.stop) begin
        //exp_wr_port.write(sb_exp_wr_item);
        exp_wr_q.push_back(sb_exp_wr_item);
        num_exp_tran++;
        `uvm_info(`gfn, $sformatf("\n\nscoreboard, exp_wr_item\n\%s",
            sb_exp_wr_item.sprint()), UVM_DEBUG)
      end
    end

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (!write && channel == DataChannel) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
            $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));

      case (csr.get_name())
        "rdata": begin
          if (host_init) begin
            if (rdata_cnt == 0) begin
              `DV_CHECK_GE_FATAL(rd_pending_q.size(), 0)
              rd_pending_item = rd_pending_q.pop_front();
            end
            // collect read data byte
            rd_pending_item.data_q.push_back(ral.rdata.get_mirrored_value());
            rdata_cnt++;
            // get all read data bytes
            if (rdata_cnt == rd_pending_item.num_data) begin
              rd_pending_item.stop = 1'b1;
              `downcast(sb_exp_rd_item, rd_pending_item.clone());
              rdata_cnt = 0;
            end
          end
        end
      endcase

      // push sb_exp_rd_item into exp_fifo
      if (host_init && sb_exp_rd_item.start && sb_exp_rd_item.stop) begin
        //exp_rd_port.write(sb_exp_rd_item);
        exp_rd_q.push_back(sb_exp_rd_item);
        num_exp_tran++;
        `uvm_info(`gfn, $sformatf("\n\nscoreboard exp_rd_item\n\%s",
            sb_exp_rd_item.sprint()), UVM_DEBUG)
      end
    end
  endtask : process_tl_access

  task compare_trans(bus_op_e dir = BusOpWrite);
    i2c_item   exp_item;
    i2c_item   dut_trn;
    forever begin
      if (dir == BusOpWrite) begin
        wr_item_fifo.get(dut_trn);
        wait(exp_wr_q.size() > 0);
        exp_item = exp_wr_q.pop_front();
      end else begin  // BusOpRead
        rd_item_fifo.get(dut_trn);
        wait(exp_rd_q.size() > 0);
        exp_item = exp_rd_q.pop_front();
      end
      if (!dut_trn.compare(exp_item)) begin
        `uvm_error(`gfn, $sformatf("%s item mismatch!\n--> EXP:\n%0s\--> DUT:\n%0s",
            (dir == BusOpWrite) ? "WRITE" : "READ", exp_item.sprint(), dut_trn.sprint()))
      end else begin
        `uvm_info(`gfn, $sformatf("direction %s item match!\n--> EXP:\n%0s\--> DUT:\n%0s",
            (dir == BusOpWrite) ? "WRITE" : "READ", exp_item.sprint(), dut_trn.sprint()), UVM_DEBUG)
      end
    end
  endtask : compare_trans

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
    rd_item_fifo.flush();
    wr_item_fifo.flush();
    exp_rd_q.delete();
    exp_wr_q.delete();
    rd_pending_q.delete();
    host_init  = 1'b0;
    tran_id    = 0;
    rdata_cnt  = 0;
    num_exp_tran = 0;
  endfunction : reset

  function void report_phase(uvm_phase phase);
    string str;

    super.report_phase(phase);
    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_DEBUG)
    if (cfg.en_scb) begin
      str = {$sformatf("\n\n*** SCOREBOARD CHECK\n")};
      str = {str, $sformatf("    - Total checked trans   %0d\n", num_exp_tran)};
      `uvm_info(`gfn, $sformatf("%s", str), UVM_LOW)
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

endclass : i2c_scoreboard
