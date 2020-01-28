// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
class i2c_rx_tx_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_rx_tx_vseq)

  rand uint  num_tx_bytes;
  rand uint  num_rx_bytes;
  rand uint  dly_to_access_reg;
  rand uint  dly_b2b_trans;
  rand uint  dly_to_access_intr;
  rand bit   wait_for_idle;
  rand uint  weight_to_skip_rx_read;

  rand bit   [TL_DW-1:0] wr_data;
  rand bit   [TL_DW-1:0] reg_val[];
  bit        [TL_DW-1:0] rd_data;

  constraint num_trans_c {
    num_trans         inside {[5:20]};
  }

  constraint wr_data_c {
    wr_data           inside {[0:65535]};
  }

  constraint dly_to_access_reg_c {
    dly_to_access_reg inside {[1:3]};
  }

  constraint reg_val_c {
    reg_val.size == 10;
    foreach (reg_val[i]) reg_val[i] inside {[1:10]};
  }

  constraint num_tx_bytes_c {
    num_tx_bytes dist {
      1       :/ 2,
      [2:10]  :/ 5,
      [11:15] :/ 5,
      [16:20] :/ 2
    };
  }

  constraint num_rx_bytes_c {
    num_rx_bytes dist {
      1       :/ 2,
      [2:10]  :/ 5,
      [11:15] :/ 5,
      [16:20] :/ 2
    };
  }

  constraint dly_b2b_trans_c {
    dly_b2b_trans dist {
      0           :/ 5,  // more back2back transaction
      [1:100]     :/ 5,
      [100:10000] :/ 2
    };
  }

  constraint dly_to_access_intr_c {
    dly_to_access_intr dist {
      0                   :/ 1,
      [1      :100]       :/ 5,
      [101    :10_000]    :/ 3,
      [10_001 :1_000_000] :/ 1
    };
  }

  constraint wait_for_idle_c {
    wait_for_idle dist {
      1       :/ 1,
      0       :/ 10
    };
  }

  constraint weight_to_skip_rx_read_c {
    // 3: read, 7: skip
    weight_to_skip_rx_read == 7;
  }

  `uvm_object_new

  task pre_start();
    super.pre_start();
    num_trans.rand_mode(0);
  endtask : pre_start

  virtual task body();
    fork
      begin
        while (do_interrupt) process_interrupts();
      end

      begin
        // repeat test sequencing upto 50 times
        for (int i = 1; i <= num_trans; i++) begin
          `DV_CHECK_RANDOMIZE_FATAL(this)
          i2c_host_init();
          `uvm_info(`gfn, $sformatf("starting run %0d/%0d", i, num_trans), UVM_MEDIUM)

          fork
            begin
              `uvm_info(`gfn, $sformatf("begin sending %0d tx bytes", num_tx_bytes), UVM_MEDIUM)
              i2c_host_write();
              `uvm_info(`gfn, $sformatf("done sending %0d tx bytes", num_tx_bytes), UVM_HIGH)
            end
            begin
              `uvm_info(`gfn, $sformatf("begin sending %0d rx bytes", num_rx_bytes), UVM_MEDIUM)
              //i2c_host_read();
              `uvm_info(`gfn, $sformatf("done sending %0d rx bytes", num_rx_bytes), UVM_HIGH)
            end
          join

          process_remaining_data();
          `uvm_info(`gfn, $sformatf("finished run %0d/%0d", i, num_trans), UVM_LOW)
        end
        do_interrupt = 0; // to end thread process_interrupts gracefully
      end
    join
  endtask : body

  virtual task i2c_host_init();
    i2c_request = i2c_wo;
    if (i2c_request == None)
      `uvm_fatal(`gfn, $sformatf("incorrect i2c_request %0s", i2c_request.name()))

    // inherite from i2c_base_vseq
    super.i2c_host_init();

    // randomize variables
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_reg)

    // program timing register
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(reg_val)
    csr_wr(.csr(ral.timing0), .value(reg_val[0]));
    csr_wr(.csr(ral.timing1), .value(reg_val[1]));
    csr_wr(.csr(ral.timing2), .value(reg_val[2]));
    csr_wr(.csr(ral.timing3), .value(reg_val[3]));
    csr_wr(.csr(ral.timing4), .value(reg_val[4]));

    cfg.clk_rst_vif.wait_clks(dly_to_access_reg);
    `uvm_info(`gfn, $sformatf("i2c host is initialized"), UVM_LOW)
  endtask : i2c_host_init

  virtual task i2c_host_read();
    if (i2c_request == i2c_ro || i2c_request == i2c_rw) begin
      super.i2c_host_read();

    end
  endtask : i2c_host_read

  virtual task i2c_host_write();
    if (i2c_request == i2c_wo || i2c_request == i2c_rw) begin
      // program fdata
      super.i2c_host_write();
    end
  endtask : i2c_host_write

  task process_interrupts();
    bit [TL_DW-1:0] intr_status, clear_intr;
    bit             clear_rx_intr, clear_tx_intr;

    // read interrupt
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_intr)
    cfg.clk_rst_vif.wait_clks(dly_to_access_intr);
    csr_rd(.ptr(ral.intr_state), .value(intr_status));
    `uvm_info(`gfn, $sformatf("intr_state 0x%08h", intr_status), UVM_LOW)

    // clear interrupt, randomly clear the interrupt that is set, and
    // don't clear the interrupt which isn't set
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(clear_intr,
                                        foreach (clear_intr[i]) {
                                          clear_intr[i] -> intr_status[i] == 1;
                                        })
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_intr)
    cfg.clk_rst_vif.wait_clks(dly_to_access_intr);

    // for fifo interrupt, parity/frame error, don't clear it at ignored period
    // as it hasn't been checked
    // TODO: update corresponding rtl changes
    clear_tx_intr = clear_intr[FmtWatermark] |
                    clear_intr[FmtOverflow];
    clear_rx_intr = clear_intr[RxWatermark] |
                    clear_intr[RxOverflow];

    wait_when_in_ignored_period(clear_tx_intr, clear_rx_intr);
    csr_wr(.csr(ral.intr_state), .value(clear_intr));
  endtask : process_interrupts

  virtual task process_remaining_data();
    // TODO
  endtask : process_remaining_data

  task post_start();
    bit [TL_DW-1:0] intr_status;
    // dut_shutdown is must for each iteration, it's called in body
    do_dut_shutdown = 0;
    // need to clear fifo when tx is disabled as data isn't sent out
    super.post_start();
  endtask
endclass : i2c_rx_tx_vseq
