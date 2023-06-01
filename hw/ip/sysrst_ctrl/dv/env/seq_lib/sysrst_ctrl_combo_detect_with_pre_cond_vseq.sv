// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence writes a random values to combo detect registers including
// precondition settings and checks for the combo detect interrupt.
class sysrst_ctrl_combo_detect_with_pre_cond_vseq extends sysrst_ctrl_base_vseq;
  `uvm_object_utils(sysrst_ctrl_combo_detect_with_pre_cond_vseq)

  `uvm_object_new
  rand uvm_reg_data_t set_action[4];
  rand bit [4:0] trigger_combo[4], trigger_combo_precondition[4];
  rand uint16_t set_duration[4], set_duration_precondition[4];
  rand uint16_t cycles, cycles_precondition;
  rand uint16_t set_pulse_width, set_key_timer, num_trans_combo_detect;
  bit ec_rst_h2l_expected = 0 ;
  bit ec_rst_l2h_expected = 0 ;
  bit disable_ec_rst_check = 0;
  // because of CDC there can be max of two cycles delay on transition of combo detect
  // input signals
  localparam uint CDC_EXP_CYCLE_TOLERANCE = 2;
  localparam uint COMBO_EXP_TOLERANCE = 4;
  localparam uint EXP_CYCLE_TOLERANCE = COMBO_EXP_TOLERANCE + CDC_EXP_CYCLE_TOLERANCE;

  constraint num_trans_c {num_trans == 50;}

  constraint num_trans_combo_detect_c {num_trans_combo_detect == 10;}

  constraint trigger_combo_precondition_c {
    foreach (trigger_combo_precondition[i]) {
      trigger_combo_precondition[i] != 0;
    }
  }

  constraint trigger_combo_c {
     foreach (trigger_combo[i]) {
       trigger_combo[i] != 0;
       (trigger_combo[i] & trigger_combo_precondition[i]) == 0;
     }
   }

  constraint set_duration_precondition_c {
    foreach (set_duration_precondition[i]) {
      set_duration_precondition[i] dist {
        [10 : 50]  :/ 95,
        [51 : 300] :/ 5
      };
    }
  }

  constraint set_duration_c {
    foreach (set_duration[i]) {
      set_duration[i] dist {
        [10 : 50 ] :/ 95,
        [51 : 300] :/ 5
      };
    }
  }

  constraint set_pulse_width_c {
    set_pulse_width dist {
      [10 : 50]  :/ 95,
      [51 : 300] :/ 5
    };
    // ec_rst will trigger a pulse, we check all the action after 4 set_duration are done
    // make the set_pulse_width larger than any of the duration, so that we can still check it's
    // value.
    foreach (set_duration[i]) {
      if (cycles > set_duration[i] + set_key_timer) {
        set_pulse_width > cycles - (set_duration[i] + set_key_timer);
      }
    }
  }

  constraint set_key_timer_c {
    set_key_timer dist {
        [10 : 50 ]  :/ 95,
        [51 : 300]  :/ 5
    };
  }

  constraint cycles_c {
    cycles >= 2; // Minimum of 2 cycles to account for CDC randomization
    foreach (set_duration[i]) {
      cycles dist {
        [1 : (set_duration[i] + set_key_timer) - 2] :/ 5,
        [(set_duration[i] + set_key_timer) + 5 : (set_duration[i] + set_key_timer) * 2] :/ 95
      };
    }
  }

  constraint cycles_precondition_c {
    foreach (set_duration_precondition[i]) {
      solve set_duration_precondition[i] before cycles_precondition;
      cycles_precondition dist {
        [1 : (set_duration_precondition[i] + set_key_timer) - 2] :/ 5,
        [(set_duration_precondition[i]) + 5 :
                     (set_duration_precondition[i] + set_key_timer) * 2]   :/ 95
      };
    }
  }

  task ec_rst_transition_check();
    `uvm_info(`gfn, "Started ec_rst_l_o transition check", UVM_LOW)
    fork
      begin : ec_rst_posedge_check
        forever begin
          @(posedge cfg.vif.ec_rst_l_out);
          wait (cfg.vif.ec_rst_l_out);
          if (!disable_ec_rst_check)
            `DV_CHECK(ec_rst_l2h_expected == 1, "Unexpected L2H transition of ec_rst_l_o");
        end
      end : ec_rst_posedge_check
      begin : ec_rst_negedge_check
        forever begin
          @(negedge cfg.vif.ec_rst_l_out);
          wait (!cfg.vif.ec_rst_l_out);
          if (!disable_ec_rst_check)
            `DV_CHECK(ec_rst_h2l_expected == 1, "Unexpected H2L transition of ec_rst_l_o");
        end
      end : ec_rst_negedge_check
    join_none
  endtask

  task automatic set_ec_rst_transition_bits(ref int start_cycles[$], uint16_t pulse_width);
    int window = 4, pulse_width_l, start_cycle;
    if (start_cycles.size() == 0) return;
    start_cycles.sort();
    start_cycle = start_cycles[0];
    // Update the aggregate pulse width in case of multiple combo blocks asserting ec_rst_l_o
    if (start_cycles.size() == 1) begin
      pulse_width_l = pulse_width;
    end
    else begin
      if ((start_cycles[0] + pulse_width) > start_cycles[$]) begin
        pulse_width_l = pulse_width + (start_cycles[$] - start_cycles[0]);
      end
    end
    `uvm_info(`gfn, $sformatf("pulse_width_l = %0d", pulse_width_l), UVM_LOW)

    fork
      begin
        // Wait 2 cycles to account for domain crossing
        cfg.clk_aon_rst_vif.wait_clks(2);
        cfg.clk_aon_rst_vif.wait_clks(start_cycle-1);
        ec_rst_h2l_expected = 1;
        `uvm_info(`gfn, "ec_rst_h2l_expected == 1", UVM_LOW)
        fork // reset bit after a number of cycles indicated by window
          begin
            cfg.clk_aon_rst_vif.wait_clks(window);
            ec_rst_h2l_expected = 0;
            `uvm_info(`gfn, "ec_rst_h2l_expected == 0", UVM_LOW)
          end
        join_none
        cfg.clk_aon_rst_vif.wait_clks(pulse_width_l);
        `uvm_info(`gfn, "ec_rst_l2h_expected == 1", UVM_LOW)
        ec_rst_l2h_expected = 1;
        fork // reset bit after a number of cycles indicated by window
          begin
            cfg.clk_aon_rst_vif.wait_clks(window);
            ec_rst_l2h_expected = 0;
            `uvm_info(`gfn, "ec_rst_l2h_expected == 0", UVM_LOW)
          end
        join_none
      end
    join_none
  endtask

  // Check for a input singal transition that triggers the combo detection logic
  function bit get_combo_trigger(int index, bit [4:0] combo_input_prev);
    logic [4:0] in;
    int count_ones_prev, count_ones;
    in[0]           = cfg.vif.key0_in;
    in[1]           = cfg.vif.key1_in;
    in[2]           = cfg.vif.key2_in;
    in[3]           = cfg.vif.pwrb_in;
    in[4]           = cfg.vif.ac_present;
    count_ones      = $countones(in & trigger_combo[index]);
    count_ones_prev = $countones(combo_input_prev & trigger_combo[index]);
    `uvm_info(`gfn, $sformatf(
              {
                "DETECTION: i:%0d, in: %5b prev_in: %5b sel:%5b,",
                "count_ones = %0d count_ones_prev = %0d "
              },
              index,
              in,
              combo_input_prev,
              trigger_combo[index],
              count_ones,
              count_ones_prev
              ), UVM_MEDIUM)
    // Check for Or'd signal transition
    return ((count_ones_prev > 0) && (count_ones == 0)) && (trigger_combo[index] != 0);
  endfunction

  // Check for a input combination that triggers the combo precondition logic
  function bit get_combo_precondition_trigger(int index);
    logic [4:0] in;
    in[0] = cfg.vif.key0_in;
    in[1] = cfg.vif.key1_in;
    in[2] = cfg.vif.key2_in;
    in[3] = cfg.vif.pwrb_in;
    in[4] = cfg.vif.ac_present;
    `uvm_info(`gfn, $sformatf(
              "PRECONDITION: i:%0d, in: %5b sel:%5b", index, in, trigger_combo_precondition[index]),
              UVM_MEDIUM)
    return ((in & trigger_combo_precondition[index]) == 0);
  endfunction

  task check_ec_rst_inactive(int max_cycle);
    cfg.clk_aon_rst_vif.wait_clks($urandom_range(0, max_cycle));
    `DV_CHECK_EQ(cfg.vif.ec_rst_l_out, 1)
  endtask

  task config_combo_register(int i, uint16_t mask = 16'hFF);
    // Select the inputs for precondition
    csr_wr(ral.com_pre_sel_ctl[i], mask & trigger_combo_precondition[i]);

    // Set the duration for precondition keys to pressed
    csr_wr(ral.com_pre_det_ctl[i], mask & set_duration_precondition[i]);
    // Select the inputs for the combo
    csr_wr(ral.com_sel_ctl[i], mask & trigger_combo[i]);

    // Set the duration for combo to pressed
    csr_wr(ral.com_det_ctl[i], mask & set_duration[i]);

    // Set the trigger action
    csr_wr(ral.com_out_ctl[i], mask & set_action[i]);
  endtask

  task config_register();
    for( int i = 0; i < 4; i++) config_combo_register(i);

    // Set the ec_rst_0 pulse width
    csr_wr(ral.ec_rst_ctl, set_pulse_width);
    `uvm_info(`gfn, $sformatf("Write data of ec_rst_ctl register:0x%0h", set_pulse_width), UVM_LOW);
    // Set the key triggered debounce timer
    csr_wr(ral.key_intr_debounce_ctl, set_key_timer);
    `uvm_info(`gfn, $sformatf("Write data of key_intr_debounce_ctl register:0x%0h", set_key_timer),
              UVM_LOW);
  endtask

  task monitor_bat_disable_L2H(int exp_cycles);
    int inactive_cycles = 0;
    int aon_period_ns = cfg.clk_aon_rst_vif.clk_period_ps / 1000;
    // Check bat_disable is low for exp_cycles. After exp_cycles+20, below will time out and fail.
    `DV_SPINWAIT(while (cfg.vif.bat_disable != 1) begin
                   cfg.clk_aon_rst_vif.wait_clks(1);
                   inactive_cycles++;
                 end , "time out waiting for bat_disable == 1",
                 aon_period_ns * (exp_cycles + 20))
    `DV_CHECK(inactive_cycles inside {[exp_cycles - EXP_CYCLE_TOLERANCE :
                                       exp_cycles + EXP_CYCLE_TOLERANCE]},
           $sformatf("bat_disable_check: inact(%0d) vs exp(%0d) +/-4", inactive_cycles, exp_cycles))
  endtask

  task monitor_rst_req_L2H(int exp_cycles);
    int inactive_cycles = 0;
    int aon_period_ns = cfg.clk_aon_rst_vif.clk_period_ps / 1000;
    // Check rst_req is low for exp_cycles. After exp_cycles+20, below will time out and fail.
    `DV_SPINWAIT(while (cfg.vif.rst_req != 1) begin
                   cfg.clk_aon_rst_vif.wait_clks(1);
                   inactive_cycles++;
                 end , "time out waiting for rst_req == 1",
                 aon_period_ns * (exp_cycles + 20))
    `DV_CHECK(inactive_cycles inside {[exp_cycles - EXP_CYCLE_TOLERANCE :
                                       exp_cycles + EXP_CYCLE_TOLERANCE]},
            $sformatf("rst_req_check: inact(%0d) vs exp(%0d) +/-4", inactive_cycles, exp_cycles))
  endtask

  task monitor_wkup_req_L2H(int exp_cycles);
    int inactive_cycles = 0;
    int aon_period_ns = cfg.clk_aon_rst_vif.clk_period_ps / 1000;
    // Check wkup_req is low for exp_cycles. After exp_cycles+20, below will time out and fail.
    `DV_SPINWAIT(while (cfg.vif.wkup_req != 1) begin
                   cfg.clk_aon_rst_vif.wait_clks(1);
                   inactive_cycles++;
                 end , "time out waiting for wkup_req == 1",
                 aon_period_ns * (exp_cycles + 20))
    `DV_CHECK(inactive_cycles inside {[exp_cycles - EXP_CYCLE_TOLERANCE :
                                       exp_cycles + EXP_CYCLE_TOLERANCE]},
            $sformatf("wkup_req_check: inact(%0d) vs exp(%0d) +/-4", inactive_cycles, exp_cycles))
  endtask

  // Sample covergroups with key selections and combo actions
  function void sample_coverpoints( int i,
    bit [4:0] trigger_combo_pre,
    bit [4:0] trigger_combo,
    bit com_out_intr,
    bit com_out_bat_disable,
    bit com_out_ec_rst,
    bit com_out_rst_req);

    // Sample aggregate key selection
    bit key0_in_sel_detect = get_field_val( ral.com_sel_ctl[i].key0_in_sel, trigger_combo);
    bit key1_in_sel_detect = get_field_val( ral.com_sel_ctl[i].key1_in_sel, trigger_combo);
    bit key2_in_sel_detect = get_field_val( ral.com_sel_ctl[i].key2_in_sel, trigger_combo);
    bit pwrb_in_sel_detect = get_field_val( ral.com_sel_ctl[i].pwrb_in_sel, trigger_combo);
    bit ac_present_sel_detect = get_field_val( ral.com_sel_ctl[i].ac_present_sel, trigger_combo);
    bit key0_in_sel_precond = get_field_val( ral.com_pre_sel_ctl[i].key0_in_sel, trigger_combo_pre);
    bit key1_in_sel_precond = get_field_val( ral.com_pre_sel_ctl[i].key1_in_sel, trigger_combo_pre);
    bit key2_in_sel_precond = get_field_val( ral.com_pre_sel_ctl[i].key2_in_sel, trigger_combo_pre);
    bit pwrb_in_sel_precond = get_field_val( ral.com_pre_sel_ctl[i].pwrb_in_sel, trigger_combo_pre);
    bit ac_present_sel_precond = get_field_val( ral.com_pre_sel_ctl[i].ac_present_sel,
                                            trigger_combo_pre);
    // Sample combo actions and key selections for each combo channel
    cov.combo_detect_action[i].sysrst_ctrl_combo_detect_action_cg.sample(
      com_out_bat_disable, com_out_intr, com_out_ec_rst, com_out_rst_req,
      key0_in_sel_detect,
      key1_in_sel_detect,
      key2_in_sel_detect,
      pwrb_in_sel_detect,
      ac_present_sel_detect,
      key0_in_sel_precond,
      key1_in_sel_precond,
      key2_in_sel_precond,
      pwrb_in_sel_precond,
      ac_present_sel_precond);
    // Sample key combination coverpoints
    cov.combo_key_combinations.sysrst_ctrl_combo_key_combinations_cg.sample(
      .bat_disable    ( com_out_bat_disable ),
      .interrupt      ( com_out_intr ),
      .ec_rst         ( com_out_rst_req ),
      .rst_req        ( com_out_rst_req ),
      .key0_in_sel    ( key0_in_sel_detect ),
      .key1_in_sel    ( key1_in_sel_detect ),
      .key2_in_sel    ( key2_in_sel_detect ),
      .pwrb_in_sel    ( pwrb_in_sel_detect ),
      .ac_present_sel ( ac_present_sel_detect ),
      .precondition_key0_in_sel ( key0_in_sel_precond ),
      .precondition_key1_in_sel ( key1_in_sel_precond ),
      .precondition_key2_in_sel ( key2_in_sel_precond ),
      .precondition_pwrb_in_sel ( pwrb_in_sel_precond ),
      .precondition_ac_present_sel ( ac_present_sel_precond) );
  endfunction

  task body();

    `uvm_info(`gfn, "Starting the body from combo detect with precondition", UVM_LOW)

    // Start sequence by releaseing ec_rst_l_o. post reset ec_rst_l_o remains asserted,
    // and must be deasserted. This is to make sure during test, the H->L and L->H transitions
    // of ec_rst_l_o can be observed
    release_ec_rst_l_o();
    // Reset combo logic input
    reset_combo_inputs();
    // Configure combo logic registers
    config_register();

    `uvm_info(`gfn, $sformatf("Value of cycles_precondition:%0d", cycles_precondition), UVM_LOW)
    `uvm_info(`gfn, $sformatf("Value of cycles:%0d", cycles), UVM_LOW)
    // It takes 2-3 clock cycles to sync the register values
    cfg.clk_aon_rst_vif.wait_clks(3);
    ec_rst_transition_check();
    repeat (num_trans) begin : main_block
      bit precond_detected_for_one_block = 1'b0;
      bit [3:0] precondition_detected = '{4{1'b0}};
      // Randomize input
      repeat ($urandom_range(1, 3)) cfg.vif.randomize_combo_input();
      // Wait for debounce + detect timer
      cfg.clk_aon_rst_vif.wait_clks(cycles_precondition);
      for (int i = 0; i < 4; i++) begin
        if (cycles_precondition > (set_duration_precondition[i] + set_key_timer) &&
              get_combo_precondition_trigger(i)) begin
          precondition_detected[i] = (trigger_combo[i] & trigger_combo_precondition[i]) == 0;
          precond_detected_for_one_block |= precondition_detected[i];
        end
      end

      if (precond_detected_for_one_block) begin : combo_detect_block
        uvm_reg_data_t  rdata;
        uint16_t       [3:0] get_duration;
        uvm_reg_data_t [3:0] get_action;
        bit [3:0]  combo_detected;
        bit [4:0]  combo_precondition_mask = 5'd0;
        bit [4:0]  get_trigger_combo[4];
        bit [4:0]  get_trigger_combo_pre[4];
        bit [4:0]  combo_input_prev;
        bit        combo_triggered[4] = '{1'b0, 1'b0, 1'b0, 1'b0};
        // Update combo_precondition_mask
        for (int i = 0; i < 4; i++) begin
          if (precondition_detected[i]) begin
            // Dont change the signals asserted for precondition
            combo_precondition_mask |= trigger_combo_precondition[i];
            `uvm_info(`gfn, $sformatf("valid precondition detected for combo channel: %0d", i),
                      UVM_LOW)
          end
          else begin
            // Disable blocks in Idle state
            csr_wr(ral.com_sel_ctl[i], 5'd0);
            csr_wr(ral.com_pre_sel_ctl[i], 5'd0);
          end
        end
        // Wait for register updates to take effect
        cfg.clk_aon_rst_vif.wait_clks(3);

        combo_precondition_mask = ~combo_precondition_mask;
        `uvm_info(`gfn, $sformatf("precondition_detected= %0x", precondition_detected), UVM_MEDIUM)
        `uvm_info(`gfn, $sformatf("combo_precondition_mask= %0x", combo_precondition_mask),UVM_LOW)

        while (precondition_detected > 0 && (combo_detected != precondition_detected) &&
               num_trans_combo_detect>0)  begin : combo_action_check
          bit bat_act_triggered, ec_act_triggered, rst_act_triggered, wkup_req_triggered;
          bit [3:0] intr_actions, intr_actions_pre_reset;
          int bat_act_occur_cyc = 0;
          int rst_req_act_occur_cyc = 0;
          int bat_act_occur_cycles[$];
          int rst_req_act_occur_cycles[$];
          int ec_rst_start_time[$];
          int wkup_req_occur_cycle = 0;
          int wkup_req_occur_cycles[$];
          int max_wait_till_next_iter = set_pulse_width;

          // Sample combo key inputs
          combo_input_prev = get_combo_input();

          // Sample the combo_intr_status covergroup to capture the trigger combo inputs
          // before randomizing the inputs
          if (cfg.en_cov) begin
            foreach (intr_actions_pre_reset[i]) begin
              intr_actions_pre_reset[i] =
                  get_field_val(ral.com_out_ctl[i].interrupt, get_action[i]);
            end
            cov.combo_intr_status.sysrst_ctrl_combo_intr_status_cg.sample(
              get_field_val(ral.combo_intr_status.combo0_h2l, rdata),
              get_field_val(ral.combo_intr_status.combo1_h2l, rdata),
              get_field_val(ral.combo_intr_status.combo2_h2l, rdata),
              get_field_val(ral.combo_intr_status.combo3_h2l, rdata),
              cfg.vif.key0_in,
              cfg.vif.key1_in,
              cfg.vif.key2_in,
              cfg.vif.pwrb_in,
              cfg.vif.ac_present,
              intr_actions_pre_reset);
          end

          // Read combo detection registers
          foreach (ral.com_det_ctl[i]) csr_rd(ral.com_det_ctl[i], get_duration[i]);
          foreach (ral.com_out_ctl[i]) csr_rd(ral.com_out_ctl[i], get_action[i]);
          foreach (ral.com_sel_ctl[i]) csr_rd(ral.com_sel_ctl[i], get_trigger_combo[i]);
          foreach (ral.com_sel_ctl[i]) csr_rd(ral.com_pre_sel_ctl[i], get_trigger_combo_pre[i]);

          // Randomize combo logic inputs except the ones asserted for precondition
          repeat ($urandom_range(1, 3)) cfg.vif.randomize_combo_input(combo_precondition_mask);
          if (combo_input_prev == get_combo_input()) break;
          // delay before doing next transitions since CDC randomization can cause
          // single cycle transitions to be ignored
          cfg.clk_aon_rst_vif.wait_clks(2);
          // Update trigger value of Combo channel and ec_rst timing check bits
          foreach (combo_triggered[i]) begin
            bit com_out_ec_rst = get_field_val(ral.com_out_ctl[i].ec_rst, get_action[i]);
            if (precondition_detected[i]) begin
              int key_detect_time = int'(get_duration[i] + set_key_timer);
              combo_triggered[i] = get_combo_trigger(i, combo_input_prev);
              if (com_out_ec_rst && combo_triggered[i] &&
                  (cycles+set_pulse_width > key_detect_time)) begin
                ec_rst_start_time.push_back(key_detect_time-1);
              end
            end
          end
          set_ec_rst_transition_bits(ec_rst_start_time, set_pulse_width);
          // Wait for debounce + detect timer
          cfg.clk_aon_rst_vif.wait_clks(cycles-2);

          // Check if the interrupt has raised.
          // NOTE: The interrupt will only raise if the interrupt combo action is set.
          for (int i = 0; i < 4; i++) begin
            if ((cycles + set_pulse_width) > (get_duration[i] + set_key_timer) &&
               combo_triggered[i])
            begin
              int key_detect_time = get_duration[i] + set_key_timer;
              bit com_out_intr = get_field_val(ral.com_out_ctl[i].interrupt, get_action[i]);
              bit com_out_bat_disable = get_field_val(ral.com_out_ctl[i].bat_disable,
                                          get_action[i]);
              bit com_out_ec_rst = get_field_val(ral.com_out_ctl[i].ec_rst, get_action[i]);
              bit com_out_rst_req = get_field_val(ral.com_out_ctl[i].rst_req, get_action[i]);

              `uvm_info(`gfn, $sformatf("valid combo input transition detected for channel :%0d",i),
                                         UVM_LOW)
              intr_actions[i] = com_out_intr;
              wkup_req_triggered |= com_out_intr;
              bat_act_triggered |= com_out_bat_disable;
              ec_act_triggered |= com_out_ec_rst;
              rst_act_triggered |= com_out_rst_req;
              if (cfg.en_cov) begin
                for (int i = 0; i < 4; i++) begin
                  sample_coverpoints( i,
                    get_trigger_combo_pre[i],
                    get_trigger_combo[i],
                    com_out_intr,
                    com_out_bat_disable,
                    com_out_ec_rst,
                    com_out_rst_req);
                end
              end
              if (com_out_bat_disable) begin
                bat_act_occur_cycles.push_back(key_detect_time);
              end
              if (com_out_rst_req) begin
                rst_req_act_occur_cycles.push_back(key_detect_time);
              end
              if (com_out_intr) begin
                wkup_req_occur_cycles.push_back(key_detect_time);
              end
              combo_detected[i]= com_out_ec_rst | com_out_bat_disable | com_out_intr |
                                 com_out_rst_req;
            end
            `uvm_info(`gfn, $sformatf("bat_act_triggered = %0b", bat_act_triggered), UVM_MEDIUM)
            `uvm_info(`gfn, $sformatf("rst_act_triggered = %0b", rst_act_triggered), UVM_MEDIUM)
          end
          // Update start cycle of output assertion
          if (bat_act_occur_cycles.size() > 0 ) begin
            bat_act_occur_cycles.sort();
            if (bat_act_occur_cycles[0] > cycles)
              bat_act_occur_cyc = bat_act_occur_cycles[0] - cycles;
          end
          if (rst_req_act_occur_cycles.size() > 0 ) begin
            rst_req_act_occur_cycles.sort();
            if (rst_req_act_occur_cycles[0] > cycles)
              rst_req_act_occur_cyc = rst_req_act_occur_cycles[0] - cycles;
          end
          if (wkup_req_occur_cycles.size() > 0 ) begin
            wkup_req_occur_cycles.sort();
            if (wkup_req_occur_cycles[0] > cycles)
              wkup_req_occur_cycle = wkup_req_occur_cycles[0] - cycles;
          end
          `uvm_info(`gfn, $sformatf("bat_act_occur_cyc = %0d", bat_act_occur_cyc), UVM_MEDIUM)
          `uvm_info(`gfn, $sformatf("rst_req_act_occur_cyc = %0d", rst_req_act_occur_cyc),
                                     UVM_MEDIUM)
          `uvm_info(`gfn, $sformatf("wkup_req_occur_cycle = %0d", wkup_req_occur_cycle),
                                     UVM_MEDIUM)
          // Check for Combo output assertions
          fork
            begin
              // Wait till next iteration
              cfg.clk_aon_rst_vif.wait_clks(set_pulse_width);
              // Reset combo inputs except the ones required to enable precondition
              reset_combo_inputs(combo_precondition_mask);
            end
            begin : bat_disable_check
              if (bat_act_triggered) begin
                if (bat_act_occur_cyc > 0) monitor_bat_disable_L2H(bat_act_occur_cyc);
                else `DV_CHECK_EQ(cfg.vif.bat_disable, 1);
              end else begin
                `DV_CHECK_EQ(cfg.vif.bat_disable, 0);
              end
            end : bat_disable_check
            begin : rst_req_check
              if (rst_act_triggered) begin
                if (rst_req_act_occur_cyc > 0) monitor_rst_req_L2H(rst_req_act_occur_cyc);
                else `DV_CHECK_EQ(cfg.vif.rst_req, 1);
              end else begin
                `DV_CHECK_EQ(cfg.vif.rst_req, 0);
              end
            end : rst_req_check
            begin : wkup_req_check
              if (wkup_req_triggered) begin
                if (wkup_req_occur_cycle > 0) monitor_wkup_req_L2H(wkup_req_occur_cycle);
                else `DV_CHECK_EQ(cfg.vif.wkup_req, 1);
              end else begin
                `DV_CHECK_EQ(cfg.vif.wkup_req, 0);
              end
            end : wkup_req_check
          join

          // Check for interrupt status after output check
          begin : intr_check
            cfg.clk_aon_rst_vif.wait_clks(1);
            csr_rd(ral.combo_intr_status, rdata);
            `DV_CHECK_EQ(rdata, intr_actions)
            if (intr_actions) begin
              check_interrupts(.interrupts(1 << IntrSysrstCtrl), .check_set(1));

              // Write to clear the interrupt.
              csr_wr(ral.combo_intr_status, rdata);

              cfg.clk_aon_rst_vif.wait_clks(5);
              // Check if the interrupt is cleared.
              csr_rd_check(ral.combo_intr_status, .compare_value(0));
              // Sample the combo intr status covergroup.
              // The combo_intr_status get updated only when the interrupt action is triggered.
              if (cfg.en_cov) begin
                cov.combo_intr_status.sysrst_ctrl_combo_intr_status_cg.sample(
                    get_field_val(ral.combo_intr_status.combo0_h2l, rdata), get_field_val(
                    ral.combo_intr_status.combo1_h2l, rdata), get_field_val(
                    ral.combo_intr_status.combo2_h2l, rdata), get_field_val(
                    ral.combo_intr_status.combo3_h2l, rdata), cfg.vif.key0_in, cfg.vif.key1_in,
                    cfg.vif.key2_in, cfg.vif.pwrb_in, cfg.vif.ac_present, intr_actions);
              end
              // Check wkup_status register
              csr_rd(ral.wkup_status, rdata);
              if (!get_field_val(ral.wkup_status.wakeup_sts, rdata)) begin
                `uvm_error(`gfn, "wkup_status.wakeup_sts set to 0")
              end
              // Write to clear wkup_req status, register is of type rw1c
              csr_wr(ral.wkup_status, uvm_reg_data_t'('d1));
              cfg.clk_aon_rst_vif.wait_clks(5);
              csr_rd_check(ral.wkup_status, .compare_value(0));
            end else begin
              check_interrupts(.interrupts(1 << IntrSysrstCtrl), .check_set(0));
              csr_rd_check(ral.wkup_status, .compare_value(0));
            end
          end : intr_check

          // Reset design for sticky combo output settings
          if (bat_act_triggered || rst_act_triggered) begin
            disable_ec_rst_check = 1;
            // Reset combo logic input
            reset_combo_inputs();
            apply_resets_concurrently();
            // Delay to avoid race condition when sending item and checking no item after
            // reset occur at the same time.
            #1ps;
            // Release ec_rst_l_o after reset
            release_ec_rst_l_o();
            // Apply_resets_concurrently will set the registers to their default values,
            // wait for sometime and reconfigure the registers for next iteration.
            config_register();
            disable_ec_rst_check = 0;
            // Reset internal variables
            precondition_detected = '{4{1'b0}};
            combo_detected = '{4{1'b0}};
            // Exit combo_action_check block
            break;
          end
          num_trans_combo_detect--;
        end : combo_action_check
      end : combo_detect_block
      // Reset combo inputs after iteration
      reset_combo_inputs();
      // Reprogram the combo selection registers
      for (int i = 0; i < 4; i++) begin
        csr_wr(ral.com_sel_ctl[i], trigger_combo[i]);
        csr_wr(ral.com_pre_sel_ctl[i], trigger_combo_precondition[i]);
      end
      cfg.clk_aon_rst_vif.wait_clks(3);
    end : main_block
  endtask : body

endclass : sysrst_ctrl_combo_detect_with_pre_cond_vseq
