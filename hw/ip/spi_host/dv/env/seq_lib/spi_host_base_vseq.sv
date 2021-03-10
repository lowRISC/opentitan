// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_host_base_vseq extends cip_base_vseq #(
    .RAL_T               (spi_host_reg_block),
    .CFG_T               (spi_host_env_cfg),
    .COV_T               (spi_host_env_cov),
    .VIRTUAL_SEQUENCER_T (spi_host_virtual_sequencer)
  );
  `uvm_object_utils(spi_host_base_vseq)
  `uvm_object_new

  // local variables
  local uint                  num_rd_words = 0;

  // random variables
  rand uint                   tx_fifo_access_dly;
  rand uint                   rx_fifo_access_dly;
  rand uint                   clear_intr_dly;
  rand uint                   num_runs;
  rand spi_regs_t             spi_host_regs;
  // constraints
  constraint num_trans_c {
    num_trans inside {[cfg.seq_cfg.host_spi_min_trans : cfg.seq_cfg.host_spi_max_trans]};
  }
  constraint num_runs_c {
    num_runs inside {[cfg.seq_cfg.host_spi_min_runs : cfg.seq_cfg.host_spi_max_runs]};
  }
  // contraints for fifo access delay
  constraint clear_intr_dly_c {
    clear_intr_dly inside {[cfg.seq_cfg.host_spi_min_dly : cfg.seq_cfg.host_spi_max_dly]};
  }
  constraint tx_fifo_access_dly_c {
    tx_fifo_access_dly inside {[cfg.seq_cfg.host_spi_min_dly : cfg.seq_cfg.host_spi_max_dly]};
  }
  constraint rx_fifo_access_dly_c {
    rx_fifo_access_dly inside {[cfg.seq_cfg.host_spi_min_dly : cfg.seq_cfg.host_spi_max_dly]};
  }
  constraint spi_host_regs_c {
    spi_host_regs.csnlead      inside {[cfg.seq_cfg.host_spi_min_csn_hcyc :
                                        cfg.seq_cfg.host_spi_max_csn_hcyc]};
    spi_host_regs.csntrail     inside {[cfg.seq_cfg.host_spi_min_csn_hcyc :
                                        cfg.seq_cfg.host_spi_max_csn_hcyc]};
    spi_host_regs.csnidle      inside {[cfg.seq_cfg.host_spi_min_csn_hcyc :
                                        cfg.seq_cfg.host_spi_max_csn_hcyc]};
    spi_host_regs.clkdiv       inside {[cfg.seq_cfg.host_spi_min_csn_hcyc :
                                        cfg.seq_cfg.host_spi_max_csn_hcyc]};
    spi_host_regs.tx1_cnt      inside {[cfg.seq_cfg.host_spi_min_tx1 :
                                        cfg.seq_cfg.host_spi_max_tx1]};
    spi_host_regs.txn_cnt      inside {[cfg.seq_cfg.host_spi_min_txn :
                                        cfg.seq_cfg.host_spi_max_txn]};
    spi_host_regs.rx_cnt       inside {[cfg.seq_cfg.host_spi_min_rx :
                                        cfg.seq_cfg.host_spi_max_rx]};
    spi_host_regs.dummy_cycles inside {[cfg.seq_cfg.host_spi_min_dummy :
                                        cfg.seq_cfg.host_spi_max_dummy]};
    spi_host_regs.tx_watermark inside {[cfg.seq_cfg.host_spi_min_txwm :
                                        cfg.seq_cfg.host_spi_max_txwm]};
    spi_host_regs.rx_watermark inside {[cfg.seq_cfg.host_spi_min_rxwm :
                                        cfg.seq_cfg.host_spi_max_rxwm]};
    spi_host_regs.speed        inside {[cfg.seq_cfg.host_spi_min_speed :
                                        cfg.seq_cfg.host_spi_max_speed]};
  }

  virtual task body();
    initialization();

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(spi_host_regs)
    `uvm_info(`gfn, $sformatf("\n  tx_watermark %0d, rx_watermark %0d",
        spi_host_regs.tx_watermark, spi_host_regs.rx_watermark), UVM_LOW)
    cfg.clk_rst_core_vif.wait_clks(100);
  endtask : body
  
  virtual task pre_start();
    // sync monitor and scoreboard setting
    cfg.m_spi_agent_cfg.en_monitor_checks = cfg.en_scb;
    `uvm_info(`gfn, $sformatf("\n  %s monitor and scoreboard",
        cfg.en_scb ? "enable" : "disable"), UVM_DEBUG)
    num_runs.rand_mode(0);
    num_trans_c.constraint_mode(0);
    super.pre_start();
  endtask : pre_start

  virtual task initialization();
    `uvm_info(`gfn, "\n  initialization spi_host", UVM_LOW)
    wait(cfg.m_spi_agent_cfg.vif.rst_n);
    `uvm_info(`gfn, "\n  initialization, out of reset", UVM_LOW)
    spi_host_init();
    spi_agent_init();
    `uvm_info(`gfn, "\n  spi_host initialization is completed", UVM_LOW)
  endtask : initialization

  // setup basic spi_host features
  virtual task spi_host_init();
    // initialize spi_host by programming CONTROL register
    ral.control.spien.set(1'b1);
    ral.control.rst_fsm.set(1'b1);
    ral.control.rst_txfifo.set(1'b1);
    ral.control.rst_rxfifo.set(1'b1);
    ral.control.passthru.set(1'b0);   // TODO: enable and verify with special_modes test
    ral.control.manual_cs.set(1'b0);  // TODO: enable and verify with special_modes test
    ral.control.mancs_en.set($urandom_range(0, 1));
    csr_update(ral.control);

    // enable then clear interrupts
    csr_wr(.ptr(ral.intr_enable), .value({TL_DW{1'b1}}));
    process_interrupts();
  endtask : spi_host_init

  virtual task spi_agent_init();
    // spi_agent is configured in the Denive mode
    spi_device_seq m_device_seq;

    m_device_seq = spi_device_seq::type_id::create("m_device_seq");
    `uvm_info(`gfn, "\n  start spi_device sequence", UVM_DEBUG)
    fork
      m_device_seq.start(p_sequencer.spi_host_sequencer_h);
    join_none
  endtask : spi_agent_init

  virtual task program_command();
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(spi_host_regs)
    `uvm_info(`gfn, $sformatf("\n  tx_watermark %0d, rx_watermark %0d",
        spi_host_regs.tx_watermark, spi_host_regs.rx_watermark), UVM_LOW)
    // TODO: V1 complete
    /*
    // CONTROLL register fields
    ral.control.tx_watermark.set(spi_host_regs.tx_watermark);
    ral.control.rx_watermark.set(spi_host_regs.rx_watermark);

    // CONFIGOPTS register fields
    ral.configopts[0].cpol.set(spi_host_regs.cpol);        // clock phase
    ral.configopts[0].cpha.set(spi_host_regs.cpha);        // sampling data phase
    ral.configopts.fullcyc.set(spi_host_regs.fullcyc);
    ral.configopts.csaat.set(spi_host_regs.csaat);
    ral.configopts.csnlead.set(spi_host_regs.csnlead);
    ral.configopts.csntrail.set(spi_host_regs.csntrail);
    ral.configopts.csnidle.set(spi_host_regs.csnidle);
    ral.configopts.clkdiv.set(spi_host_regs.clkdiv);
    // TXDATA register fields
    ral.txdata.set($urandom_range(0, (1 << TL_DW) - 1));
    // COMMAND register fields
    ral.command.tx1_cnt.set(spi_host_regs.tx1_cnt);
    ral.command.txn_cnt.set(spi_host_regs.txn_cnt);
    ral.command.rx_cnt.set(spi_host_regs.rx_cnt);
    num_rd_words = $floor(spi_host_regs.rx_cnt / 2);    // word-level data
    `uvm_info(`gfn, $sformatf("\n  rx_cnt %0d, num_rd_words %0d",
        spi_host_regs.rx_cnt, num_rd_words), UVM_DEBUG)
    ral.command.dummy_cycles.set(spi_host_regs.dummy_cycles);
    ral.command.fulldplx.set(spi_host_regs.fulldplx);
    ral.command.highz.set(spi_host_regs.highz);
    ral.command.speed.set(spi_host_regs.speed);         // spi mode
    ral.command.go.set(1'b1);                           // submit command to tx_fifo (self-clear)

    // update spi_host registers
      csr_update(ral.control);
    csr_update(ral.configopts);
    //csr_update(ral.txdata);                           // TODO: error in spi_host.hjson
    csr_update(ral.command);                            // command is finally submitted

    // update spi_agent registers
    cfg.m_spi_agent_cfg.spi_agent_regs = spi_host_regs;
    */
  endtask : program_command

  virtual task send_transactions();
    `uvm_info(`gfn, "\n  send_transactions task running ...", UVM_DEBUG)

    for (uint cur_tran = 1; cur_tran <= num_trans; cur_tran++) begin
      csr_spinwait(.ptr(ral.status.txfull), .exp_data(1'b0));
      program_command();
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(tx_fifo_access_dly)
      cfg.clk_rst_vif.wait_clks(tx_fifo_access_dly);
    end
  endtask : send_transactions

  virtual task get_transactions(uint num_rd_words);
    bit [TL_DW-1:0] rxdata;
    
    while (!num_rd_words) begin
      csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b1));
      csr_rd(.ptr(ral.rxdata), .value(rxdata));
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rx_fifo_access_dly)
      cfg.clk_rst_vif.wait_clks(rx_fifo_access_dly);
      num_rd_words--;
    end
  endtask : get_transactions

  // read interrupts and randomly clear interrupts if set
  virtual task process_interrupts();
    bit [TL_DW-1:0] intr_state, intr_clear;

    // read interrupt
    csr_rd(.ptr(ral.intr_state), .value(intr_state));
    // clear interrupt if it is set
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(intr_clear,
                                       foreach (intr_clear[i]) {
                                           intr_state[i] -> intr_clear[i] == 1;
                                       })
    
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(clear_intr_dly)
    cfg.clk_rst_vif.wait_clks(clear_intr_dly);
    csr_wr(.ptr(ral.intr_state), .value(intr_clear));
  endtask : process_interrupts

  // override apply_reset to handle core_reset domain
  virtual task apply_reset(string kind = "HARD");
    fork
      if (kind == "HARD" || kind == "TL_IF") begin
        super.apply_reset("HARD");
      end
      if (kind == "HARD" || kind == "CORE_IF") begin
        cfg.clk_rst_core_vif.apply_reset();
      end
    join
  endtask

  // override wait_for_reset to to handle core_reset domain
  virtual task wait_for_reset(string reset_kind     = "HARD",
                              bit wait_for_assert   = 1,
                              bit wait_for_deassert = 1);

    fork
      if (reset_kind == "HARD" || reset_kind == "TL_IF") begin
        super.wait_for_reset(reset_kind, wait_for_assert, wait_for_deassert);
      end
      if (reset_kind == "HARD" || reset_kind == "CORE_IF") begin
        if (wait_for_assert) begin
          `uvm_info(`gfn, "waiting for core rst_n assertion...", UVM_MEDIUM)
          @(negedge cfg.clk_rst_core_vif.rst_n);
        end
        if (wait_for_deassert) begin
          `uvm_info(`gfn, "waiting for core rst_n de-assertion...", UVM_MEDIUM)
          @(posedge cfg.clk_rst_core_vif.rst_n);
        end
        `uvm_info(`gfn, "core wait_for_reset done", UVM_HIGH)
      end
    join
  endtask : wait_for_reset

  // phase alignment for resets signal of core and bus domain
  virtual task do_phase_align_reset(bit en_phase_align_reset = 1'b0);
    if (en_phase_align_reset) begin
      fork
        cfg.clk_rst_vif.wait_clks($urandom_range(5, 10));
        cfg.clk_rst_core_vif.wait_clks($urandom_range(5, 10));
      join
    end
  endtask : do_phase_align_reset

endclass : spi_host_base_vseq
