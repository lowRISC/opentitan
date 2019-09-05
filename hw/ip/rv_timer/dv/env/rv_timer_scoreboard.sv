// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_timer_scoreboard extends cip_base_scoreboard #(.CFG_T (rv_timer_env_cfg),
                                                        .RAL_T (rv_timer_reg_block),
                                                        .COV_T (rv_timer_env_cov));

  `uvm_component_utils(rv_timer_scoreboard)
  `uvm_component_new

  // local variables
  local uint64 prescale[NUM_HARTS];
  local uint64 step[NUM_HARTS];
  local uint64 timer_val[NUM_HARTS];
  local uint64 compare_val[NUM_HARTS][NUM_TIMERS];
  local uint   num_clks[NUM_HARTS][NUM_TIMERS];
  local bit [NUM_TIMERS-1:0] en_timers[NUM_HARTS];
  local bit [NUM_TIMERS-1:0] en_timers_prev[NUM_HARTS];
  local bit [NUM_TIMERS-1:0] en_interrupt[NUM_HARTS];
  local bit [NUM_TIMERS-1:0] ignore_period[NUM_HARTS];

  // expected values
  local uint intr_status_exp[NUM_HARTS];

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    compute_and_check_interrupt();
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg csr;
    string  csr_name;
    bit     do_read_check = 1'b1;
    bit     write = item.is_write();

    // if access was to a valid csr, get the csr handle
    if (item.a_addr inside {cfg.csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(item.a_addr);
      `DV_CHECK_NE_FATAL(csr, null)
      csr_name = csr.get_name();
    end
    if (csr == null) begin
      // we hit an oob addr - expect error response and return
      `DV_CHECK_EQ(item.d_error, 1'b1)
      return;
    end

    if (!write && channel == AddrChannel) begin
      if (!uvm_re_match("intr_state*", csr_name)) begin
        for (int i = 0; i < NUM_HARTS; i++) begin
          if (csr_name == $sformatf("intr_state%0d", i)) begin
            if ((intr_status_exp[i] != csr.get_mirrored_value()) & (ignore_period[i] == 'b0)) begin
              csr.predict(.value(intr_status_exp[i]), .kind(UVM_PREDICT_READ));
            end
            break;
          end
          else if (i == (NUM_HARTS - 1)) begin
            `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
          end
        end
      end
    end

    // grab write transactions from address channel; grab completed transactions from data channel

    // if incoming access is a write to a valid csr, then make updates right away
    if (write && channel == AddrChannel) begin
      csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask));

      // process the csr req
      case (1)
        (!uvm_re_match("ctrl*", csr_name)): begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            for (int j = 0; j < NUM_TIMERS; j++) begin
              en_timers[i][j] = get_reg_fld_mirror_value(ral, "ctrl", $sformatf("active%0d", j));
            end
          end
        end
        (!uvm_re_match("cfg*", csr_name)): begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            step[i]     = get_reg_fld_mirror_value(ral, $sformatf("cfg%0d", i), "step");
            prescale[i] = get_reg_fld_mirror_value(ral, $sformatf("cfg%0d", i), "prescale");
          end
        end
        (!uvm_re_match("timer_v_lower*", csr_name)): begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            timer_val[i][31:0] = get_reg_fld_mirror_value(
                                     ral, $sformatf("timer_v_lower%0d", i), "v");
          end
        end
        (!uvm_re_match("timer_v_upper*", csr_name)): begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            timer_val[i][63:32] = get_reg_fld_mirror_value(
                                      ral, $sformatf("timer_v_upper%0d", i), "v");
          end
        end
        (!uvm_re_match("compare_lower*", csr_name)): begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            for (int j = 0; j < NUM_TIMERS; j++) begin
              compare_val[i][j][31:0] = get_reg_fld_mirror_value(
                                            ral, $sformatf("compare_lower%0d_%0d", i, j), "v");
            end
          end
        end
        (!uvm_re_match("compare_upper*", csr_name)): begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            for (int j = 0; j < NUM_TIMERS; j++) begin
              compare_val[i][j][63:32] = get_reg_fld_mirror_value(
                                             ral, $sformatf("compare_upper%0d_%0d", i, j), "v");
            end
          end
        end
        (!uvm_re_match("intr_enable*", csr_name)): begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            for (int j = 0; j < NUM_TIMERS; j++) begin
              en_interrupt[i][j] = get_reg_fld_mirror_value(
                                       ral, $sformatf("intr_enable%0d", i), $sformatf("ie%0d", j));
            end
          end
        end
        (!uvm_re_match("intr_state*", csr_name)): begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            string intr_state_str = $sformatf("intr_state%0d", i);
            if (csr_name == intr_state_str) begin
              // Intr_state reg is W1C, update expected status with RAL mirrored val
              intr_status_exp[i] = get_reg_fld_mirror_value(ral, intr_state_str);
              break;
            end
          end
        end
        (!uvm_re_match("intr_test*", csr_name)): begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            string intr_test_str = $sformatf("intr_test%0d", i);
            if (csr_name == intr_test_str) begin
              intr_status_exp[i] = get_reg_fld_mirror_value(ral, intr_test_str);
              // this field is WO - always returns 0
              csr.predict(.value(0), .kind(UVM_PREDICT_WRITE));
              break;
            end
          end
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
        end
      endcase
    end

    if (channel == DataChannel) begin
      // Check all interrupts in DataChannel of every Read/Write
      check_interrupt_pin();

      // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
      if (!write) begin
        // exclude read check for timer_val* reg if read happended when timer is enabled
        if (!uvm_re_match("timer_v_*", csr_name)) begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            if (!uvm_re_match($sformatf("timer_v_*%0d", i), csr_name)) begin
              if (en_timers[i] == 0) begin
                `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data)
              end
              else begin
                if (!uvm_re_match("timer_v_lower*", csr_name)) timer_val[i][31:0] = item.d_data;
                else timer_val[i][63:32] = item.d_data;
              end
              break;
            end
            else if (i == (NUM_HARTS - 1)) begin
              `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
            end
          end
        end
        // Read happened for other registers
        else if (do_read_check) begin
          `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data)
        end

        csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ));
      end
    end
  endtask

  // Task : compute_and_check_interrupt
  // wait for expected # of clocks and check for interrupt state reg and pin
  virtual task compute_and_check_interrupt();

    fork
      begin
        forever begin : compute_num_clks
          // calculate number of clocks required to have interrupt
          @(en_timers or step or prescale or timer_val or compare_val);
          wait(under_reset == 0);
          foreach (en_timers[i, j]) begin
            uint64 mtime_diff = compare_val[i][j] - timer_val[i];
            num_clks[i][j] = ((mtime_diff / step[i]) +
                              ((mtime_diff % step[i]) != 0)) * (prescale[i] + 1) + 1;
          end
        end // compute_num_clks
      end
    join_none

    forever begin : wait_for_interrupt
      @(en_timers or under_reset);
      wait(under_reset == 0);
      // fork a thread for enabled timer on all enabled hart
      foreach (en_timers[i, j]) begin
        automatic int a_i = i;
        automatic int a_j = j;
        fork
          if (en_timers[a_i][a_j] & !en_timers_prev[a_i][a_j]) begin
            fork
              begin
                uint64 count = 0;
                uint64 num_clks_latest = num_clks[a_i][a_j];
                uint   num_clks_prev   = num_clks[a_i][a_j];
                en_timers_prev[a_i][a_j] = 1'b1;
                forever begin
                  @cfg.clk_rst_vif.cb;
                  count = count + 1;
                  if (num_clks_prev != num_clks[a_i][a_j]) begin
                    num_clks_latest = count + num_clks[a_i][a_j];
                    num_clks_prev = num_clks[a_i][a_j];
                  end
                  if (count >= num_clks_latest) break;
                end
                // enabling one clock cycle of ignore period
                ignore_period[a_i][a_j] = 1'b1;
                `uvm_info(`gfn, $sformatf("Timer expired check for interrupt"), UVM_LOW)
                // Update exp val and predict it in read address_channel
                intr_status_exp[a_i][a_j] = 1'b1;
                check_interrupt_pin();
                @cfg.clk_rst_vif.cb;
                ignore_period[a_i][a_j] = 1'b0;
              end
              begin
                wait((en_timers[a_i][a_j] == 0) | (under_reset == 1));
              end
            join_any
            en_timers_prev[a_i][a_j] = 1'b0;
            // kill forked threads if timer disabled or interrupt occured or under reset
            disable fork;
          end
        join_none
      end
    end // wait_for_interrupt
  endtask : compute_and_check_interrupt

  // function : check_interrupt_pin
  // check all interrupt output pins with expected intr state & pin enable
  function void check_interrupt_pin();
    for (int i = 0; i < NUM_HARTS; i++) begin
      for (int j = 0; j < NUM_TIMERS; j++) begin
        int intr_pin_idx = i * NUM_HARTS + j;
        `DV_CHECK_CASE_EQ(cfg.intr_vif.sample_pin(.idx(intr_pin_idx)),
                          (intr_status_exp[i][j] & en_interrupt[i][j]))
      end
    end
  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset the local values
    step            = '{default:1};
    prescale        = '{default:0};
    timer_val       = '{default:0};
    compare_val     = '{default:'1};
    en_timers       = '{default:0};
    en_interrupt    = '{default:0};
    intr_status_exp = '{default:0};
    ignore_period   = '{default:0};
    en_timers_prev  = '{default:0};
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
  endfunction

endclass
