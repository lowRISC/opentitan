// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_host_tx_rx_vseq extends spi_host_base_vseq;
  `uvm_object_utils(spi_host_tx_rx_vseq)
  `uvm_object_new

  semaphore spi_host_atomic = new(1);

  spi_host_status_t status;
  uvm_sequence_state_enum seq_state;


  virtual task body();
    fork
      begin: isolation_fork
        fork
          start_reactive_seq();
        join_none
        fork
          begin
            wait_ready_for_command();
            start_spi_host_trans();
            disable fork;
          end
        join
      end
    join
  endtask : body


  virtual task start_spi_host_trans();

    program_spi_host_regs();
    wait_ready_for_command();
    csr_rd(.ptr(ral.status), .value(status));
    generate_transaction();

    send_trans(transaction);
    cfg.clk_rst_vif.wait_clks(1000);

    // wait for all accesses to complete
    wait_no_outstanding_access();

    // read out status/intr_state CSRs to check
    check_status_and_clear_intrs();

  endtask : start_spi_host_trans


  // sending tx requests to the agent
  virtual task send_trans(spi_transaction_item trans);
    spi_segment_item segment = new();

    while (trans.segments.size() > 0) begin
      // wait on DUT ready
      segment = trans.segments.pop_back();
      wait_ready_for_command();
      // lock fifo to this seq
      spi_host_atomic.get(1);
      // write data to fifo
      write_data_to_fifo(segment.spi_data);
      program_command_reg(segment.command_reg);

      spi_host_atomic.put(1);
    end
  endtask : send_trans


  virtual task generate_transaction();
    transaction_init();
    `DV_CHECK_RANDOMIZE_FATAL(transaction)
    `uvm_info(`gfn, $sformatf("%s",transaction.convert2string()), UVM_HIGH);
  endtask // generate_transaction

endclass : spi_host_tx_rx_vseq
