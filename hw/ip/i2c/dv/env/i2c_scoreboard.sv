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

  // interrupt bit vector
  local bit [NumI2cIntr-1:0] intr_exp;

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
    fork
      super.run_phase(phase);
      compare_trans(BusOpWrite);
      compare_trans(BusOpRead);
    join
  endtask : run_phase

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg   csr;
    i2c_item  sb_exp_wr_item;
    i2c_item  sb_exp_rd_item;
    bit       fmt_overflow;
    bit       do_read_check = 1'b0;    // TODO: Enable this bit later
    bit       write = item.is_write();

    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);
    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("\naccess unexpected addr 0x%0h", csr_addr))
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
                  // if not a chained read (stop is issued)
                  if (exp_rd_item.stop) begin
                    `uvm_info(`gfn, $sformatf("\nscoreboard, partial exp_rd_item\n\%s",
                        exp_rd_item.sprint()), UVM_DEBUG)
                    `downcast(tmp_rd_item, exp_rd_item.clone());
                    rd_pending_q.push_back(tmp_rd_item);
                    `uvm_info(`gfn, $sformatf("\nrd_pending_q.push_back"), UVM_DEBUG)
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
          if (cfg.en_cov) begin
            cov.fmt_fifo_level_cg.sample(.irq(cfg.intr_vif.pins[FmtWatermark]),
                                         .lvl(ral.fifo_status.fmtlvl.get_mirrored_value()),
                                         .rst(fmtrst_val));
          end
          if (cfg.en_cov) begin
            cov.rx_fifo_level_cg.sample(.irq(cfg.intr_vif.pins[RxWatermark]),
                                        .lvl(ral.fifo_status.rxlvl.get_mirrored_value()),
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
              // for on-the-fly reset, immediately finish task to avoid blocking
              wait(rd_pending_q.size() > 0 || cfg.under_reset);              
              if (cfg.under_reset) return; 
              rd_pending_item = rd_pending_q.pop_front();
            end
            rd_pending_item.data_q.push_back(ral.rdata.get_mirrored_value());
            rdata_cnt++;
            `uvm_info(`gfn, $sformatf("\nscoreboard, rd_pending_item\n\%s",
                rd_pending_item.sprint()), UVM_DEBUG)
            // get complete read transactions
            if (rdata_cnt == rd_pending_item.num_data) begin
              rd_pending_item.stop = 1'b1;
              `downcast(sb_exp_rd_item, rd_pending_item.clone());
              exp_rd_q.push_back(sb_exp_rd_item);
              num_exp_tran++;
              `uvm_info(`gfn, $sformatf("\nscoreboard, push to queue, exp_rd_item\n\%s",
                  sb_exp_rd_item.sprint()), UVM_DEBUG)
              rdata_cnt = 0;
            end
          end
        end
      endcase
    end // end of read data phase
  endtask : process_tl_access

  task compare_trans(bus_op_e dir = BusOpWrite);
    i2c_item   exp_trn;
    i2c_item   dut_trn;
    forever begin
      if (dir == BusOpWrite) begin
        wr_item_fifo.get(dut_trn);
        wait(exp_wr_q.size() > 0);
        exp_trn = exp_wr_q.pop_front();
      end else begin  // BusOpRead
        rd_item_fifo.get(dut_trn);
        wait(exp_rd_q.size() > 0);
        exp_trn = exp_rd_q.pop_front();
      end
      // when rx_fifo is overflow, drop the last byte from dut_trn
      if (cfg.seq_cfg.en_rx_overflow && dut_trn.bus_op == BusOpRead) begin
        dut_trn.data_q.pop_back();
        dut_trn.num_data--;
      end
      if (!dut_trn.compare(exp_trn)) begin
        if (!check_overflow_data_fmt_fifo(exp_trn, dut_trn)) begin  // see description below
          `uvm_error(`gfn, $sformatf("\ndirection %s item mismatch!\n--> EXP:\n%0s\--> DUT:\n%0s",
              (dir == BusOpWrite) ? "WRITE" : "READ", exp_trn.sprint(), dut_trn.sprint()))
        end
      end else begin
        `uvm_info(`gfn, $sformatf("\ndirection %s item match!\n--> EXP:\n%0s\--> DUT:\n%0s",
            (dir == BusOpWrite) ? "WRITE" : "READ", exp_trn.sprint(), dut_trn.sprint()), UVM_DEBUG)
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
    `uvm_info(`gfn, "\n>>> finish resetting scoreboard", UVM_DEBUG)
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

endclass : i2c_scoreboard
