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
  local bit [NUM_HARTS-1:0][NUM_TIMERS-1:0] en_timers;
  local bit [NUM_HARTS-1:0][NUM_TIMERS-1:0] en_timers_prev;
  local bit [NUM_HARTS-1:0][NUM_TIMERS-1:0] en_interrupt;
  local bit [NUM_HARTS-1:0][NUM_TIMERS-1:0] ignore_period;
  local bit [NUM_HARTS-1:0] num_clk_update_due;
  local bit ctimecmp_update_on_fly;

  // expected values
  local uint intr_status_exp[NUM_HARTS];

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    compute_and_check_interrupt();
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    string  csr_name;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs[ral_name]}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
      csr_name = csr.get_name();
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    if (!write && channel == AddrChannel) begin
      if (!uvm_re_match("intr_state*", csr_name)) begin
        for (int i = 0; i < NUM_HARTS; i++) begin
          if (csr_name == $sformatf("intr_state%0d", i)) begin
            if ((intr_status_exp[i] != csr.get_mirrored_value()) & (ignore_period[i] == 'b0)) begin
              void'(csr.predict(.value(intr_status_exp[i]), .kind(UVM_PREDICT_READ)));
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
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));

      // process the csr req
      case (1)
        (!uvm_re_match("ctrl*", csr_name)): begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            for (int j = 0; j < NUM_TIMERS; j++) begin
              en_timers[i][j] = get_reg_fld_mirror_value(ral, "ctrl", $sformatf("active_%0d", j));
            end
            //Sample all timers active coverage for each hart
            if (cfg.en_cov) cov.ctrl_reg_cov_obj[i].timer_active_cg.sample(en_timers[i]);
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
            num_clk_update_due[i] = 1'b1;
          end
        end
        (!uvm_re_match("timer_v_upper*", csr_name)): begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            timer_val[i][63:32] = get_reg_fld_mirror_value(
                                      ral, $sformatf("timer_v_upper%0d", i), "v");
            num_clk_update_due[i] = 1'b1;
          end
        end
        (!uvm_re_match("compare_lower*", csr_name)): begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            for (int j = 0; j < NUM_TIMERS; j++) begin
              int timer_idx = i * NUM_TIMERS + j;
              string compare_lower_str = $sformatf("compare_lower%0d_%0d", i, j);
              if (csr_name == compare_lower_str) begin
                compare_val[i][j][31:0] = csr.get_mirrored_value();
                if (en_timers[i][j] == 0) begin
                  // Reset the interrupt when mtimecmp is updated and timer is not active
                  intr_status_exp[i][j] = 0;
                  if (cfg.en_cov) begin
                    cov.sticky_intr_cov[{"rv_timer_sticky_intr_pin",
                                        $sformatf("%0d", timer_idx)}].sample(1'b0);
                  end
                end else begin
                  // intr stays sticky if timer is active
                  ctimecmp_update_on_fly = 1;
                  if (cfg.en_cov) begin
                    cov.sticky_intr_cov[{"rv_timer_sticky_intr_pin",
                                        $sformatf("%0d", timer_idx)}].sample(intr_status_exp[i][j]);
                  end
                end
                break;
              end
            end
          end
        end
        (!uvm_re_match("compare_upper*", csr_name)): begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            for (int j = 0; j < NUM_TIMERS; j++) begin
              int timer_idx = i * NUM_TIMERS + j;
              string compare_upper_str = $sformatf("compare_upper%0d_%0d", i, j);
              if (csr_name == compare_upper_str) begin
                compare_val[i][j][63:32] = csr.get_mirrored_value();
                if (en_timers[i][j] == 0) begin
                  // Reset the interrupt when mtimecmp is updated and timer is not active
                  intr_status_exp[i][j] = 0;
                  if (cfg.en_cov) begin
                    cov.sticky_intr_cov[{"rv_timer_sticky_intr_pin",
                                        $sformatf("%0d", timer_idx)}].sample(1'b0);
                  end
                end else begin
                  // intr stays sticky if timer is active
                  ctimecmp_update_on_fly = 1;
                  if (cfg.en_cov) begin
                    cov.sticky_intr_cov[{"rv_timer_sticky_intr_pin",
                                        $sformatf("%0d", timer_idx)}].sample(intr_status_exp[i][j]);
                  end
                end
                break;
              end
            end
          end
        end
        (!uvm_re_match("intr_enable*", csr_name)): begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            for (int j = 0; j < NUM_TIMERS; j++) begin
              en_interrupt[i][j] = get_reg_fld_mirror_value(
                                       ral, $sformatf("intr_enable%0d", i), $sformatf("ie_%0d", j));
            end
          end
        end
        (!uvm_re_match("intr_state*", csr_name)): begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            string intr_state_str = $sformatf("intr_state%0d", i);
            if (csr_name == intr_state_str) begin
              // Intr_state reg is W1C, update expected status with RAL mirrored val
              for (int j = 0; j < NUM_TIMERS; j++) begin
                int timer_idx = i * NUM_TIMERS + j;
                if (item.a_data[j] == 1) begin
                  if (en_timers[i][j] == 0) begin
                    intr_status_exp[i][j] = 0;
                    if (cfg.en_cov) begin
                      cov.sticky_intr_cov[{"rv_timer_sticky_intr_pin",
                                          $sformatf("%0d", timer_idx)}].sample(1'b0);
                    end
                  end
                  else if (cfg.en_cov) begin // sticky interrupt
                    cov.sticky_intr_cov[{"rv_timer_sticky_intr_pin",
                                        $sformatf("%0d", timer_idx)}].sample(1'b1);
                  end
                end
              end
              break;
            end
          end
        end
        (!uvm_re_match("intr_test*", csr_name)): begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            string intr_test_str = $sformatf("intr_test%0d", i);
            if (csr_name == intr_test_str) begin
              uint intr_test_val = item.a_data;
              for (int j = 0 ; j < NUM_TIMERS; j++) begin
                int intr_pin_idx = i * NUM_TIMERS + j;
                if (intr_test_val[j]) intr_status_exp[i][j] = intr_test_val[j];
                //Sample intr_test coverage for each bit of test reg
                if (cfg.en_cov) cov.intr_test_cg.sample(intr_pin_idx, intr_test_val[j],
                                                        en_interrupt[i][j], intr_status_exp[i][j]);
              end
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
      // Check all interrupts in DataChannel of every Read/Write except when ctimecmp updated
      // during timer active. This scenario is checked in base sequence by reading the intr_state.
      // Ignored checking here because sticky intr_pin update has one cycle delay.
      // TODO #1464: temp constraint, if support external reg, this can be removed
      if (!ctimecmp_update_on_fly) check_interrupt_pin();
      ctimecmp_update_on_fly = 0;

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
                if (!uvm_re_match("timer_v_lower*", csr_name)) begin
                  timer_val[i][31:0] = item.d_data;
                  // on timer_val read update num_clks
                  num_clk_update_due[i] = 1'b1;
                end
                else begin
                  timer_val[i][63:32] = item.d_data;
                end
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

        void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
      end
    end
  endtask

  // Task : compute_and_check_interrupt
  // wait for expected # of clocks and check for interrupt state reg and pin
  virtual task compute_and_check_interrupt();
    bit [NUM_HARTS-1:0][NUM_TIMERS-1:0] reset_count;

    fork
      begin
        forever begin : compute_num_clks
          // calculate number of clocks required to have interrupt
          @(en_timers or num_clk_update_due);
          wait(under_reset == 0);
          foreach (en_timers[i, j]) begin
            uint64 mtime_diff = compare_val[i][j] - timer_val[i];
            num_clks[i][j] = ((mtime_diff / step[i]) +
                              ((mtime_diff % step[i]) != 0)) * (prescale[i] + 1) + 1;
          end
          // reset count if timer is enabled and num_clks got updated
          for (int i = 0; i < NUM_HARTS; i++) begin
            if (num_clk_update_due[i]) reset_count[i] = en_timers[i];
          end
          num_clk_update_due = '0;
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
                en_timers_prev[a_i][a_j] = 1'b1;
                forever begin
                  @cfg.clk_rst_vif.cb;
                  count = count + 1;
                  if (reset_count[a_i][a_j] == 1'b1) begin
                    count = 0;
                    reset_count[a_i][a_j] = 1'b0;
                  end
                  if (count >= num_clks[a_i][a_j]) break;
                end
                // enabling one clock cycle of ignore period
                ignore_period[a_i][a_j] = 1'b1;
                `uvm_info(`gfn, $sformatf("Timer expired check for interrupt"), UVM_MEDIUM)
                // Update exp val and predict it in read address_channel
                intr_status_exp[a_i][a_j] = 1'b1;
                check_interrupt_pin();
                if (cfg.en_cov) begin
                  int timer_idx = a_i * NUM_TIMERS + a_j;
                  //Sample cfg coverage for each timer
                  cov.cfg_values_cov_obj[timer_idx].timer_cfg_cg.sample(step[a_i],
                      prescale[a_i], timer_val[a_i], compare_val[a_i][a_j]);
                  //Sample toggle coverage for each prescale bit
                  for (int i = 0; i < 12; i++) begin
                    cov.rv_timer_prescale_values_cov_obj[a_i][i].sample(prescale[a_i][i]);
                  end
                end
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

  // task : check_interrupt_pin
  // check all interrupt output pins with expected intr state & pin enable
  // according to issue #841, interrupt will have one clock cycle delay
  task check_interrupt_pin();
    fork
      begin
        // store the `intr_status_exp` and `en_interrupt` values into an automatic local variable
        // in case the values are being updated during the one clock cycle wait.
        automatic uint stored_intr_status_exp[NUM_HARTS] = intr_status_exp;
        automatic bit [NUM_HARTS-1:0][NUM_TIMERS-1:0] stored_en_interrupt = en_interrupt;
        cfg.clk_rst_vif.wait_clks(1);
        if (!under_reset) begin
          for (int i = 0; i < NUM_HARTS; i++) begin
            for (int j = 0; j < NUM_TIMERS; j++) begin
              int intr_pin_idx = i * NUM_TIMERS + j;
              `DV_CHECK_CASE_EQ(cfg.intr_vif.sample_pin(.idx(intr_pin_idx)),
                                (stored_intr_status_exp[i][j] & stored_en_interrupt[i][j]))
              // Sample interrupt and interrupt pin coverage for each timer
              if (cfg.en_cov) begin
                cov.intr_cg.sample(intr_pin_idx, stored_en_interrupt[i][j],
                                   stored_intr_status_exp[i][j]);
                cov.intr_pins_cg.sample(intr_pin_idx, cfg.intr_vif.sample_pin(.idx(intr_pin_idx)));
              end
            end
          end
        end
      end
    join_none
  endtask

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
    ctimecmp_update_on_fly = 0;
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
  endfunction

endclass
