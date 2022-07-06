// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence has the tasks that combine basic tasks
// from base_vseq into more elaborate actions
// such as build a full spi transaction (which is consist of cmd/addr/dummy/data segments
// or transmit a transaction which is setting up the dut, program fifo and enable transmit
// for each individual segment.
//
// these task can be easily leveraged to build more complex sequences
//

class spi_host_tx_rx_vseq extends spi_host_base_vseq;
  `uvm_object_utils(spi_host_tx_rx_vseq)
  `uvm_object_new

  semaphore spi_host_atomic = new(1);


  virtual task start_spi_host_trans(int num_transactions, bit wait_ready = 1'b1);
    spi_host_status_t status;
    program_spi_host_regs();
    if (wait_ready) wait_ready_for_command();
    csr_rd(.ptr(ral.status), .value(status));

    for (int n = 0; n < num_transactions; n++) begin
      generate_transaction();
      send_trans(transaction, wait_ready);
      if (wait_ready) wait_ready_for_command();
    end
  endtask


  virtual task read_rx_fifo();
    bit [7:0] read_q[$];
    bit active = 0;
    bit rxempty;
    spi_host_status_t status;

    csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0));
    forever begin
      do begin
        csr_rd(.ptr(ral.status), .value(status));
        for (int i = 0; i < status.rx_qd; i++) begin
          access_data_fifo(read_q, RxFifo);
        end
      end while (status.rx_qd > 0);
      if (!status.active && status.rxempty && (status.rx_qd == 0)) begin
        break;
      end
    end  // forever loop

    // wait for all accesses to complete
    wait_no_outstanding_access();

    // read out status/intr_state CSRs to check
    check_status_and_clear_intrs();

  endtask

  // sending tx requests to the agent
  virtual task send_trans(spi_transaction_item trans, bit wait_ready = 1'b1);
    spi_segment_item segment = new();
    while (trans.segments.size() > 0) begin
      // wait on DUT ready
      segment = trans.segments.pop_back();
      if (wait_ready) wait_ready_for_command();
      // lock fifo to this seq
      spi_host_atomic.get(1);
      // write data to fifo
      if (segment.command_reg.direction != RxOnly) begin
        access_data_fifo(segment.spi_data, TxFifo);
      end
      program_command_reg(segment.command_reg);
      spi_host_atomic.put(1);
    end
  endtask : send_trans

  virtual task txfifo_fill();
    spi_segment_item segment = new();
    spi_host_atomic.get(1);
    access_data_fifo(segment.spi_data, TxFifo);
    spi_host_atomic.put(1);
  endtask : txfifo_fill

  virtual task generate_transaction();
    transaction_init();
    `DV_CHECK_RANDOMIZE_FATAL(transaction)
  endtask

  task check_event(uvm_reg_field fld, bit intr_value, bit state_value);
    spi_host_intr_state_t intr_state;
    uvm_reg_field enable_fld;
    if (fld == ral.status.active) begin
      enable_fld = ral.event_enable.get_field_by_name("idle");
    end
    else begin
      enable_fld = ral.event_enable.get_field_by_name(fld.get_name);
    end
    csr_rd_check(.ptr(fld), .compare_value(state_value));
    if ((enable_fld != null) && enable_fld.get()) begin
      bit enable = `gmv(enable_fld);
      check_interrupts(1 << intr_state.spi_event, intr_value & enable);
    end else begin
      check_interrupts(1 << intr_state.spi_event, 0);
    end
  endtask

  task check_error(uvm_reg_field fld, bit value);
    spi_host_intr_state_t intr_state;
    uvm_reg_field enable_fld = ral.error_enable.get_field_by_name(fld.get_name);
    csr_rd_check(.ptr(fld), .compare_value(value));
      if ((enable_fld != null) && enable_fld.get()) begin
        bit enable = `gmv(enable_fld);
        `DV_CHECK(ral.intr_enable.predict(.value(intr_enable.error), .kind(UVM_PREDICT_DIRECT)))
        check_interrupts(1 << intr_state.error, value & enable);
      end else begin
        check_interrupts(1 << intr_state.error, 0);
      end
  endtask
endclass : spi_host_tx_rx_vseq
