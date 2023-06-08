// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Trigger a software reset (CONTROL.SW_RST) randomly during an ongoing transaction

// - Check rx and tx queues are empty post SW_RST application
// From Documentation (hw/ip/spi_host/data/spi_host.hjson):
// >  In the current implementation, the CDC FIFOs are drained (not reset).
// >  Therefore, software must confirm that both FIFO's are empty before releasing the IP from reset
//
class spi_host_sw_reset_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_sw_reset_vseq)
  `uvm_object_new

  function void pre_randomize();
    super.pre_randomize();
    cfg.seq_cfg.host_spi_min_trans = 1;
    cfg.seq_cfg.host_spi_max_trans = 2;
    cfg.seq_cfg.host_spi_min_runs = 2;
    cfg.seq_cfg.host_spi_max_runs = 5;
  endfunction

  virtual task body();
    int edges_until_sw_rst;
    for (int i = 0; i < num_runs; i++) begin : for_num_runs
      `uvm_info(`gfn, $sformatf("Starting run %0d/%0d now!", i, num_runs), UVM_LOW)
      fork begin : isolation_fork
        fork
          start_reactive_seq();
        join_none

        begin
          wait_ready_for_command();
          start_spi_host_trans(num_trans);
          fork
            begin
              // Read data out of RXFIFO once the DUT becomes active
              read_rx_fifo(); // Returns when status.active == 0 + rxdata is cleared out.
            end

            // Happy-path : Start transaction(s), wait for DUT to become idle again.
            // Then trigger a sw_reset event.
            begin
              csr_spinwait(.ptr(ral.status.active), .exp_data(1'b0), .backdoor(1));
              if (edges_until_sw_rst > 0) begin
                // Look at the edge-counter to check if the other thread is triggering the sw_reset.
                // (The other thread will only trigger when the counter reaches 0)
                // This stops both threads from trying to write to the register.
                csr_utils_pkg::wait_no_outstanding_access();
                `uvm_info(`gfn, "Triggering CONTROL.SW_RST now!", UVM_LOW)
                spi_host_init();
              end
            end

            // Sad-path : Wait for a random-number of SCK-edges into the transaction, then
            // trigger CONTROL.SW_RESET.
            // > If we randomize to a larger number of SCK edges than the transaction, the above
            //   block will end, causing this block to get disabled.
            begin
              `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(edges_until_sw_rst,
                edges_until_sw_rst inside { [40 : 120] };) // TODO(#18886) Examine txn len for range
              while (edges_until_sw_rst > 0) begin
                // TODO(#18886) The below statement assumes CSB[0], future work may break this.
                cfg.m_spi_agent_cfg.wait_sck_edge(DrivingEdge, 2'b00);
                edges_until_sw_rst--;
              end
              csr_utils_pkg::wait_no_outstanding_access();
              `uvm_info(`gfn, "Triggering CONTROL.SW_RST now!", UVM_LOW)
              spi_host_init();
            end
          join_any;
        end

        // Wait for no outstanding accesses before using 'disable fork' to kill the path
        // which did not join.
        csr_utils_pkg::wait_no_outstanding_access();
        disable fork;
      end : isolation_fork join

      cfg.clk_rst_vif.wait_clks($urandom_range(100, 200));
      // Confirm that both FIFO's are empty before releasing the IP from reset.
      csr_rd_check(.ptr(ral.status.rxempty), .compare_value(1'b1));
      csr_rd_check(.ptr(ral.status.txempty), .compare_value(1'b1));

    end : for_num_runs
  endtask : body
endclass : spi_host_sw_reset_vseq
