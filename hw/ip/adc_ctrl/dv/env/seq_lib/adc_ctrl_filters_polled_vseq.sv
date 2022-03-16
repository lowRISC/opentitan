// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Polled filters test sequence
class adc_ctrl_filters_polled_vseq extends adc_ctrl_base_vseq;

  `uvm_object_utils(adc_ctrl_filters_polled_vseq)

  constraint num_trans_c {num_trans inside {[1 : 3]};}

  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    fork
      check_adc_ctrl_status();
    join_none
    cfg.testmode = AdcCtrlTestmodeNormal;
  endtask

  virtual task post_start();
    super.post_start();
    // Kill background processes
    disable check_adc_ctrl_status;
  endtask

  virtual task body();
    uvm_reg_data_t rdata;
    adc_ctrl_random_ramp_vseq random_ramp_vseq;

    repeat (num_trans) begin

      // Make sure ADC is off
      csr_wr(ral.adc_en_ctl, 'h0);

      // Sample coverage
      if (cfg.en_cov) begin
        cov.sample_cfg_cov();
      end

      // Set up the adc_ctrl registers
      configure_adc_ctrl();

      // Clear interrupt status reg
      csr_wr(ral.adc_intr_status, '1);

      // Check interrupt status is cleared
      csr_rd_check(.ptr(ral.adc_intr_status), .compare_value(0),
                   .err_msg(called_from(`__FILE__, `__LINE__)));

      // Start ADC
      ral.adc_en_ctl.adc_enable.set(1);
      case (cfg.testmode)
        AdcCtrlTestmodeOneShot: begin
          ral.adc_en_ctl.oneshot_mode.set(1);
          ral.adc_pd_ctl.lp_mode.set(0);
        end
        AdcCtrlTestmodeNormal: begin
          ral.adc_en_ctl.oneshot_mode.set(0);
          ral.adc_pd_ctl.lp_mode.set(0);
        end
        AdcCtrlTestmodeLowpower: begin
          ral.adc_en_ctl.oneshot_mode.set(0);
          ral.adc_pd_ctl.lp_mode.set(1);
        end
        default: `uvm_fatal(`gfn, "Undefined test mode")
      endcase
      csr_wr(ral.adc_pd_ctl, ral.adc_pd_ctl.get());
      csr_wr(ral.adc_en_ctl, ral.adc_en_ctl.get());

      // Hook to do things immediately after the adc_ctrl is enabled
      post_adc_ctrl_enable();

      // Send randomized ramp on all channels - rising
      `uvm_create_obj(adc_ctrl_random_ramp_vseq, random_ramp_vseq)
      random_ramp_vseq.set_sequencer(p_sequencer);
      // verilog_format: off - avoid bad formatting
      `DV_CHECK_RANDOMIZE_WITH_FATAL(random_ramp_vseq,
        ramp_min      == 0;
        ramp_max      == adc_value_t'('1);
        ramp_step_min == 0;
        ramp_step_max == 5;
        ramp_rising   == 1;)
      // verilog_format: on
      random_ramp_vseq.start(p_sequencer, this);
      `uvm_info(`gfn, random_ramp_vseq.sprint(uvm_default_line_printer), UVM_MEDIUM)


      // Send randomized ramp on all channels - falling
      `uvm_create_obj(adc_ctrl_random_ramp_vseq, random_ramp_vseq)
      random_ramp_vseq.set_sequencer(p_sequencer);
      // verilog_format: off - avoid bad formatting
      `DV_CHECK_RANDOMIZE_WITH_FATAL(random_ramp_vseq,
        ramp_min      == 0;
        ramp_max      == adc_value_t'('1);
        ramp_step_min == 0;
        ramp_step_max == 5;
        ramp_rising   == 0;)
      // verilog_format: on
      random_ramp_vseq.start(p_sequencer, this);
      `uvm_info(`gfn, random_ramp_vseq.sprint(uvm_default_line_printer), UVM_MEDIUM)
      // Now turn off ADC_CTRL
      adc_ctrl_off();

      // FSM reset to synchronise RTL & model
      do_adc_fsm_reset();

      // Re-randomize configuration if enabled
      if (!cfg.filters_fixed) `DV_CHECK_RANDOMIZE_FATAL(cfg);

    end
    // A short delay to allow all CDC to complete
    cfg.clk_aon_rst_vif.wait_clks($urandom_range(10, 15));
  endtask : body

  // Check the status registers after every ADC sample (all channels)
  virtual task check_adc_ctrl_status();
    uvm_reg_data_t rdata;
    forever begin
      // Wait for all channels
      wait_all_rx();
      // Delay to allow register to be updated via clock domain crossing
      cfg.clk_aon_rst_vif.wait_clks(10);
      csr_rd(ral.filter_status, rdata);
      // Randomly erase status bits by writing to filter_status
      if ($urandom_range(0, 10) > 9) begin
        csr_wr(ral.filter_status, $urandom());
      end
    end
  endtask

  // Hook to do things immediately after the adc_ctrl is enabled
  virtual task post_adc_ctrl_enable();
  endtask

endclass : adc_ctrl_filters_polled_vseq
