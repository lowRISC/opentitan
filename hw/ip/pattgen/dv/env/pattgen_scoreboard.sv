// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_scoreboard extends cip_base_scoreboard #(
    .CFG_T(pattgen_env_cfg),
    .RAL_T(pattgen_reg_block),
    .COV_T(pattgen_env_cov)
  );
  `uvm_component_utils(pattgen_scoreboard)
  `uvm_component_new

  // TLM fifos hold the transactions sent by monitor
  uvm_tlm_analysis_fifo #(pattgen_item) item_fifo[NUM_PATTGEN_CHANNELS];

  // interrupt bit vector
  local bit [NumPattgenIntr-1:0] intr_exp;
  // queues hold expected transactions for all channels
  local pattgen_item exp_item_q[NUM_PATTGEN_CHANNELS][$];
  // local variables
  local pattgen_channel_cfg channel_cfg[NUM_PATTGEN_CHANNELS-1:0];
  local bit [NumPattgenIntr-1:0] intr_exp_at_addr_phase;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    foreach (channel_cfg[i]) begin
      item_fifo[i] = new($sformatf("item_fifo[%0d]", i), this);
      channel_cfg[i] = pattgen_channel_cfg::type_id::create($sformatf("channel_cfg[%d]", i));
    end
  endfunction : build_phase

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    forever begin
      `DV_SPINWAIT_EXIT(
        for (uint i = 0; i < NUM_PATTGEN_CHANNELS; i++) begin
          fork
            automatic uint channel = i;
            compare_trans(channel);
          join_none
        end
        wait fork;,
        @(negedge cfg.clk_rst_vif.rst_n),
      )
    end
  endtask : run_phase

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg         csr;
    bit [TL_DW-1:0] reg_value;
    bit             do_read_check = 1'b1;
    bit             write = item.is_write();

    bit addr_phase_write = (write && channel  == AddrChannel);
    bit data_phase_read  = (!write && channel == DataChannel);

    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);
    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("\naccess unexpected addr 0x%0h", csr_addr))
    end

    // address write phase
    if (addr_phase_write) begin
      // if incoming access is a write to a valid csr, then make updates right away
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));

      // process the csr req
      // for write, update local variable and fifo at address phase
      // for read, update predication at address phase and compare at data phase
      case (csr.get_name())
        "size": begin
          reg_value = ral.size.get_mirrored_value();
          channel_cfg[0].len  = get_field_val(ral.size.len_ch0,  reg_value);
          channel_cfg[0].reps = get_field_val(ral.size.reps_ch0, reg_value);
          channel_cfg[1].len  = get_field_val(ral.size.len_ch1,  reg_value);
          channel_cfg[1].reps = get_field_val(ral.size.reps_ch1, reg_value);
          `uvm_info(`gfn, $sformatf("\n  scb: ral.size len0 %0d reps0 %0d len1 %0d reps1 %0d",
              channel_cfg[0].len, channel_cfg[0].reps,
              channel_cfg[1].len, channel_cfg[1].reps), UVM_DEBUG)
        end
        "prediv_ch0": begin
          channel_cfg[0].prediv = ral.prediv_ch0.get_mirrored_value();
        end
        "data_ch0_0": begin
          channel_cfg[0].data[31:0] = ral.data_ch0_0.get_mirrored_value();
        end
        "data_ch0_1": begin
          channel_cfg[0].data[63:32] = ral.data_ch0_1.get_mirrored_value();
        end
        "prediv_ch1": begin
          channel_cfg[1].prediv = ral.prediv_ch1.get_mirrored_value();
        end
        "data_ch1_0": begin
          channel_cfg[1].data[31:0] = ral.data_ch1_0.get_mirrored_value();
        end
        "data_ch1_1": begin
          channel_cfg[1].data[63:32] = ral.data_ch1_1.get_mirrored_value();
        end
        "ctrl": begin
          reg_value = ral.ctrl.get_mirrored_value();
          channel_cfg[0].enable   = bit'(get_field_val(ral.ctrl.enable_ch0,   reg_value));
          channel_cfg[1].enable   = bit'(get_field_val(ral.ctrl.enable_ch1,   reg_value));
          channel_cfg[0].polarity = bit'(get_field_val(ral.ctrl.polarity_ch0, reg_value));
          channel_cfg[1].polarity = bit'(get_field_val(ral.ctrl.polarity_ch1, reg_value));
          `uvm_info(`gfn, $sformatf("\n  scb: ctrl reg %b", reg_value[3:0]), UVM_DEBUG);
          for (uint i = 0; i < NUM_PATTGEN_CHANNELS; i++) begin
            // channel is started
            if (channel_cfg[i].enable && !channel_cfg[i].start && !channel_cfg[i].stop) begin
              channel_cfg[i].start = 1'b1;
              `uvm_info(`gfn, $sformatf("\n  scb: channel %0d is started", i), UVM_DEBUG)
            end
            // channel is operating but incorrectly disabled -> error injected
            if (!channel_cfg[i].enable && channel_cfg[i].start && !channel_cfg[i].stop) begin
              channel_cfg[i].stop = 1'b1;
              `uvm_info(`gfn, $sformatf("\n  scb: channel config %0d\n%s",
                  i, channel_cfg[i].convert2string()), UVM_DEBUG)
              generate_exp_items(.channel(i), .error_injected(1'b1));
            end
          end
        end
        "intr_test": begin
          bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
          intr_exp |= item.a_data;
          if (cfg.en_cov) begin
            pattgen_intr_e intr;
            foreach (intr_exp[i]) begin
              intr = pattgen_intr_e'(i); // cast to enum to get interrupt name
              cov.intr_test_cg.sample(intr, item.a_data[i], intr_en[i], intr_exp[i]);
            end
          end
        end
        "intr_enable": begin
          // no special handle is needed
        end
        "intr_state": begin
          bit[TL_DW-1:0] intr_wdata = item.a_data;
          fork begin
            bit [NumPattgenIntr-1:0] pre_intr = intr_exp;
            cfg.clk_rst_vif.wait_clks(1);
            intr_exp &= ~intr_wdata;
          end join_none
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("\n  scb: write to invalid csr: %0s", csr.get_full_name()))
        end
      endcase
    end

    // On reads and & data phase, if do_read_check, is set, then
    // check mirrored_value against item.d_data
    if (data_phase_read) begin
      case (csr.get_name())
        "intr_state": begin
          pattgen_intr_e     intr;
          bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
          do_read_check = 1'b0;
          // done_ch0/done_ch1 is asserted to indicate a pattern is completely generated
          reg_value = item.d_data;
          channel_cfg[0].stop = bit'(get_field_val(ral.intr_state.done_ch0, reg_value));
          channel_cfg[1].stop = bit'(get_field_val(ral.intr_state.done_ch1, reg_value));
          `uvm_info(`gfn, $sformatf("\n  scb: read intr_state %b%b",
              channel_cfg[1].stop, channel_cfg[0].stop), UVM_DEBUG)
          for (uint i = 0; i < NUM_PATTGEN_CHANNELS; i++) begin
            generate_exp_items(.channel(i), .error_injected(1'b0));
          end
          foreach (intr_exp[i]) begin
            intr = pattgen_intr_e'(i); // cast to enum to get interrupt name
            if (cfg.en_cov) begin
              cov.intr_cg.sample(intr, intr_en[intr], intr_exp[intr]);
              cov.intr_pins_cg.sample(intr, cfg.intr_vif.pins[intr]);
            end
          end
        end
        "ctrl", "size", "intr_test", "intr_enable",
        "prediv_ch0", "data_ch0_0", "data_ch0_1",
        "prediv_ch1", "data_ch1_0", "data_ch1_1": begin
          // no special handle is needed
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("\n  scb: read from invalid csr: %0s", csr.get_full_name()))
        end
      endcase

      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
            $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask : process_tl_access

  task compare_trans(uint channel);
    pattgen_item exp_item;
    pattgen_item dut_item;

    forever begin
      item_fifo[channel].get(dut_item);
      wait(exp_item_q[channel].size() > 0);
      exp_item = exp_item_q[channel].pop_front();

      if (!dut_item.compare(exp_item)) begin
        `uvm_error(`gfn, $sformatf("\n--> channel %0d item mismatch!\n--> EXP:\n%s\--> DUT:\n%s",
            channel, exp_item.sprint(), dut_item.sprint()))
      end else begin
        `uvm_info(`gfn, $sformatf("\n--> channel %0d item match!\n--> EXP:\n%s\--> DUT:\n%s",
            channel, exp_item.sprint(), dut_item.sprint()), UVM_DEBUG)
      end
    end
  endtask : compare_trans

  virtual function void generate_exp_items(uint channel, bit error_injected = 1'b0);
    if (channel_cfg[channel].start && channel_cfg[channel].stop) begin
      if (!error_injected) begin
        pattgen_item exp_item;
        exp_item = pattgen_item::type_id::create("exp_item");
        // see the specification document, the effective values of prediv, len, and reps
        // are incremented from the coresponding register values
        for (uint r = 0; r <= channel_cfg[channel].reps; r++) begin
          for (uint l = 0; l <= channel_cfg[channel].len; l++) begin
            exp_item.data_q.push_back(channel_cfg[channel].data[l]);
          end
        end
        exp_item_q[channel].push_back(exp_item);
        `uvm_info(`gfn, $sformatf("\n--> scb: get exp_item for channel %0d\n%s",
            channel, exp_item.sprint()), UVM_DEBUG)
      end else begin
        `uvm_info(`gfn, $sformatf("\n--> scb: drop exp_item for channel %0d", channel), UVM_DEBUG)
      end
      channel_cfg[channel].reset_channel_config();
    end
  endfunction : generate_exp_items

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    for (uint i = 0; i < NUM_PATTGEN_CHANNELS; i++) begin
      item_fifo[i].flush();
      exp_item_q[i].delete();
      channel_cfg[i].reset_channel_config(kind);
    end
  endfunction : reset

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    for (int i = 0; i < NUM_PATTGEN_CHANNELS; i++) begin
      `DV_EOT_PRINT_Q_CONTENTS(pattgen_item, exp_item_q[i])
      `DV_EOT_PRINT_TLM_FIFO_CONTENTS(pattgen_item, item_fifo[i])
    end
  endfunction : check_phase

  function void report_phase(uvm_phase phase);
    string str;
    super.report_phase(phase);
    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_DEBUG)
    if (cfg.en_scb) begin
      str = {$sformatf("\n*** SCOREBOARD CHECK\n")};
      `uvm_info(`gfn, $sformatf("%s", str), UVM_DEBUG)
    end
  endfunction : report_phase
endclass : pattgen_scoreboard
