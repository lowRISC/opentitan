// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_timer_base_vseq extends cip_base_vseq #(
        .CFG_T               (rv_timer_env_cfg),
        .RAL_T               (rv_timer_reg_block),
        .COV_T               (rv_timer_env_cov),
        .VIRTUAL_SEQUENCER_T (rv_timer_virtual_sequencer)
    );
  `uvm_object_utils(rv_timer_base_vseq)

  // random delay between consecutive transactions
  rand uint delay;

  constraint delay_c {
    delay dist {
      0                   :/ 1,
      [1      :100]       :/ 1,
      [101    :10_000]    :/ 8,
      [10_001 :1_000_000] :/ 1
    };
  }

  // hart specific parameters
  // These need to be NUM_HARTS size arrays; but the current assumption is these values will be the
  // same for all harts.
  bit [TL_DW-1:0] max_prescale;
  bit [TL_DW-1:0] max_step;

  `uvm_object_new

  function void pre_randomize();
    super.pre_randomize();
    max_prescale = (1 << p_sequencer.cfg.ral.cfg0.prescale.get_n_bits()) - 1;
    max_step = (1 << p_sequencer.cfg.ral.cfg0.step.get_n_bits()) - 1;
  endfunction

  task pre_start();
    super.pre_start();
  endtask

  // cfg rv_timer - set a particular timer active or inactive
  virtual task cfg_timer(int hart = 0, int timer = 0, bit enable = 1'b1);
    uvm_reg       ctrl_rg;
    uvm_reg_field active_fld;
    `DV_CHECK_LT_FATAL(hart, NUM_HARTS)
    `DV_CHECK_LT_FATAL(timer, NUM_TIMERS)
    ctrl_rg = ral.get_reg_by_name($sformatf("ctrl"));
    `DV_CHECK_NE_FATAL(ctrl_rg, null)
    active_fld = ctrl_rg.get_field_by_name($sformatf("active_%0d", timer));
    `DV_CHECK_NE_FATAL(active_fld, null)
    active_fld.set(enable);
    csr_update(.csr(ctrl_rg));
  endtask

  // cfg rv_timer prescaler and count step
  virtual task cfg_hart(int hart = 0, int prescale = 1, int step = 1);
    uvm_reg hart_cfg_rg;
    `DV_CHECK_LT_FATAL(hart, NUM_HARTS)
    `DV_CHECK_LE_FATAL(prescale, max_prescale)
    `DV_CHECK_LE_FATAL(step, max_step)
    hart_cfg_rg = ral.get_reg_by_name($sformatf("cfg%0d", hart));
    `DV_CHECK_NE_FATAL(hart_cfg_rg, null)
    hart_cfg_rg.get_field_by_name("prescale").set(prescale);
    hart_cfg_rg.get_field_by_name("step").set(step);
    csr_update(.csr(hart_cfg_rg));
  endtask

  // set timer value for a particular HART
  virtual task set_timer_val(int hart = 0, bit [63:0] val);
    uvm_reg timer_val_l_rg;
    uvm_reg timer_val_u_rg;
    `DV_CHECK_LT_FATAL(hart, NUM_HARTS)
    timer_val_l_rg = ral.get_reg_by_name($sformatf("timer_v_lower%0d", hart));
    timer_val_u_rg = ral.get_reg_by_name($sformatf("timer_v_upper%0d", hart));
    `DV_CHECK_NE_FATAL(timer_val_l_rg, null)
    `DV_CHECK_NE_FATAL(timer_val_u_rg, null)
    timer_val_l_rg.set(val[31:0]);
    timer_val_u_rg.set(val[63:32]);
    csr_update(.csr(timer_val_l_rg));
    csr_update(.csr(timer_val_u_rg));
  endtask

  // set timer value for a particular timer
  virtual task set_compare_val(int hart = 0, int timer = 0, bit [63:0] val);
    uvm_reg compare_val_l_rg;
    uvm_reg compare_val_u_rg;
    `DV_CHECK_LT_FATAL(hart, NUM_HARTS)
    `DV_CHECK_LT_FATAL(timer, NUM_TIMERS)
    compare_val_l_rg = ral.get_reg_by_name($sformatf("compare_lower%0d_%0d", hart, timer));
    compare_val_u_rg = ral.get_reg_by_name($sformatf("compare_upper%0d_%0d", hart, timer));
    `DV_CHECK_NE_FATAL(compare_val_l_rg, null)
    `DV_CHECK_NE_FATAL(compare_val_u_rg, null)
    compare_val_l_rg.set(val[31:0]);
    compare_val_u_rg.set(val[63:32]);
    csr_update(.csr(compare_val_l_rg));
    csr_update(.csr(compare_val_u_rg));
  endtask

  // configure interrupt
  virtual task cfg_interrupt(int hart = 0, int timer = 0, bit enable = 1'b1);
    uvm_reg       intr_en_rg;
    uvm_reg_field timer_intr_en_fld;
    int           intr_pin_idx = hart * NUM_TIMERS + timer;
    `DV_CHECK_LT_FATAL(hart, NUM_HARTS)
    `DV_CHECK_LT_FATAL(timer, NUM_TIMERS)
    intr_en_rg = ral.get_reg_by_name($sformatf("intr_enable%0d", hart));
    `DV_CHECK_NE_FATAL(intr_en_rg, null)
    timer_intr_en_fld = intr_en_rg.get_field_by_name($sformatf("ie_%0d", timer));
    `DV_CHECK_NE_FATAL(timer_intr_en_fld, null)
    timer_intr_en_fld.set(enable);
    csr_update(.csr(intr_en_rg));
    // also check intr output, if disabled
    if (!enable) begin
      `DV_CHECK_EQ(cfg.intr_vif.sample_pin(.idx(intr_pin_idx)), 1'b0)
    end
  endtask

  // check if interrupt fired
  virtual task check_interrupt(int hart = 0, int timer = 0, bit exp_intr_state, bit exp_intr_pin);
    uvm_reg       intr_state_rg;
    uvm_reg_field timer_intr_state_fld;
    int           intr_pin_idx = hart * NUM_TIMERS + timer;
    `DV_CHECK_LT_FATAL(hart, NUM_HARTS)
    `DV_CHECK_LT_FATAL(timer, NUM_TIMERS)
    intr_state_rg = ral.get_reg_by_name($sformatf("intr_state%0d", hart));
    `DV_CHECK_NE_FATAL(intr_state_rg, null)
    timer_intr_state_fld = intr_state_rg.get_field_by_name($sformatf("is_%0d", timer));
    `DV_CHECK_NE_FATAL(timer_intr_state_fld, null)
    void'(timer_intr_state_fld.predict(.value(exp_intr_state), .kind(UVM_PREDICT_DIRECT)));
    csr_rd_check(.ptr(intr_state_rg), .compare_vs_ral(1));
    // also check intr output
    `DV_CHECK_EQ(cfg.intr_vif.sample_pin(.idx(intr_pin_idx)), exp_intr_pin)
  endtask

  // task to write 1 to clear and read the interrupt status register
  virtual task clear_intr_state(int hart = 0, int timer = 0);
    uvm_reg         intr_state_rg;
    uvm_reg_field   is_fld;
    bit [TL_DW-1:0] status;
    bit [TL_DW-1:0] wr_value;
    `DV_CHECK_LT_FATAL(hart, NUM_HARTS)
    `DV_CHECK_LT_FATAL(timer, NUM_TIMERS)
    // randomly clear the intr by writing intr_state or mtimecmp
    intr_state_rg = ral.get_reg_by_name($sformatf("intr_state%0d", hart));
    `DV_CHECK_NE_FATAL(intr_state_rg, null)

    if ($urandom_range(0, 1)) begin
      wr_value = 1 << timer;
      csr_wr(.ptr(intr_state_rg), .value(wr_value));
    end else begin
      wr_value = $urandom();
      set_compare_val(hart, timer, wr_value);
      // wait one clk cycle then check intr, to ensure get the sticky interrupt value
      cfg.clk_rst_vif.wait_clks(1);
    end
    csr_rd(.ptr(intr_state_rg), .value(status));
  endtask

  // poll a intr_status continuously until it reads the expected value.
  virtual task intr_state_spinwait(input int  hart              = 0,
                                   input uint exp_data          = 0,
                                   input uint spinwait_delay_ns = 0,
                                   input uint timeout_ns        = 10_000_000); // 10ms
    bit [TL_DW-1:0] read_data;
    bit reset_asserted;
    uvm_reg intr_state_rg;
    intr_state_rg = ral.get_reg_by_name($sformatf("intr_state%0d", hart));
    `DV_CHECK_NE_FATAL(intr_state_rg, null)
    fork
      begin : isolation_fork
        fork
          begin
            wait(cfg.clk_rst_vif.rst_n == 0);
            reset_asserted = 1'b1;
          end
        join_none
        fork
          while (1) begin
            csr_rd(.ptr(intr_state_rg), .value(read_data));
            if (spinwait_delay_ns) #(spinwait_delay_ns * 1ns);
            if ((read_data == exp_data) | (reset_asserted == 1)) break;
          end
          begin
            wait_timeout(timeout_ns, "intr_state_spinwait",
                         $sformatf("timeout %0s (addr=0x%0h) == 0x%0h",
                         intr_state_rg.get_full_name(), intr_state_rg.get_address(), exp_data));
          end
        join_any
        disable fork;
      end : isolation_fork
    join
  endtask

  // task to read interrup status reg for given Hart
  virtual task read_intr_status_reg(input  int  hart = 0,
                                    output uint status_val);
    uvm_reg intr_state_rg;
    intr_state_rg = ral.get_reg_by_name($sformatf("intr_state%0d", hart));
    `DV_CHECK_NE_FATAL(intr_state_rg, null)
    csr_rd(.ptr(intr_state_rg), .value(status_val));
  endtask : read_intr_status_reg

  // task to read timer value reg for given Hart
  virtual task read_timer_val_reg(input  int    hart = 0,
                                  output uint64 mtime_val);
    bit [TL_DW-1:0] read_data;
    uvm_reg timer_val_l_rg;
    uvm_reg timer_val_u_rg;
    timer_val_l_rg = ral.get_reg_by_name($sformatf("timer_v_lower%0d", hart));
    timer_val_u_rg = ral.get_reg_by_name($sformatf("timer_v_upper%0d", hart));
    `DV_CHECK_NE_FATAL(timer_val_l_rg, null)
    `DV_CHECK_NE_FATAL(timer_val_u_rg, null)
    csr_rd(.ptr(timer_val_u_rg), .value(read_data));
    mtime_val[63:32] = read_data;
    csr_rd(.ptr(timer_val_l_rg), .value(read_data));
    mtime_val[31:0] = read_data;
  endtask : read_timer_val_reg

  // Status register read random for passed clks
  virtual task status_read_for_clks(int hart = 0, int clks);
    bit stop_reading;
    fork
      begin
        cfg.clk_rst_vif.wait_clks(clks);
        stop_reading = 1'b1;
      end
      begin
        forever begin
          // read will trigger check in scoreboard
          uint rd_data;
          read_intr_status_reg(.hart(hart), .status_val(rd_data));
          fork
            begin : isolation_fork
              fork
                begin
                  delay = $urandom_range(1, 10000);
                  #(delay * 1ns);
                end
                wait(stop_reading == 1);
              join_any
              disable fork;
            end : isolation_fork
          join
          if (stop_reading == 1) break;
        end
      end
    join
  endtask : status_read_for_clks

endclass : rv_timer_base_vseq
