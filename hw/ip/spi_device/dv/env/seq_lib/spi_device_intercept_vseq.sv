// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Enable intercept to test these commands processed in spi_device module
// - status, read jedec, read fsdp, read mailbox
class spi_device_intercept_vseq extends spi_device_pass_cmd_filtering_vseq;
  `uvm_object_utils(spi_device_intercept_vseq)
  `uvm_object_new

  // can override this queue to increase the chance to test these opcodes in extended vseq
  bit [7:0] target_ops[$] = {READ_STATUS_1, READ_STATUS_2, READ_STATUS_3,
                             READ_JEDEC,
                             READ_SFDP,
                             READ_CMD_LIST};

  rand bit use_target_op;
  constraint opcode_c {
    solve use_target_op before opcode;
    if (use_target_op) {
      opcode inside {target_ops};
    } else {
      opcode inside {valid_opcode_q} &&
      !(opcode inside {target_ops});
    }
  }

  constraint mailbox_addr_size_c {
    read_addr_size_type == ReadAddrWithinMailbox;
  }

  virtual task pre_start();
    allow_intercept = 1;
    super.pre_start();
  endtask

  virtual task random_cycle_delay();
    int unsigned cycle_delay;
    if(!std::randomize(cycle_delay) with { cycle_delay dist {[1:10] := 80,
                                                             [11:20] := 15,
                                                             [21:50] := 4,
                                                             [51:90] := 1
                                                             };  })
      `uvm_fatal(`gfn, "Randomization Failure")
    `uvm_info(`gfn, $sformatf("Inserting %0d TL-UL cycle delays",cycle_delay), UVM_DEBUG)
    cfg.clk_rst_vif.wait_clks(cycle_delay);
  endtask

  // randomly set flash_status for every spi transaction
  virtual task spi_host_xfer_flash_item(bit [7:0] op, uint payload_size,
                                        bit [31:0] addr, bit wait_on_busy = 1);
    typedef enum  {sequential_access, concurrent_access, two_writes, wrong} access_option_t;

    bit                                            delay_free;
    bit                                            spi_command_finished;
    access_option_t             access_option;
    // Note: there shouldn't be two flash_status writes in a row without SPI command in between
    // The RTL could absord a second write, but it wouldn't be correct operation in terms of SW
    // behaviour. In theory, one could write the upper-bits of flash_status, followed by another
    // write to clear the busy bit (the case is commented out just in case the stimulus is needed
    // to close coverage).
    //
    // In practice, SW writes to flash_status should only occur as a response to a command which
    // sets the busy bit.
    // When the RTL processes a read_status command internally, it commits a whole byte of status
    // bits to return to the host. So if SW were to write flash_status whilst the host was sending
    // a READ_STATUS command, and the host left the CSB line low "fow a while" expecting for
    // instance to read the busy bit unset, the host would see complete bytes written to
    // flash_status and not a byte made of two partial different writes

    access_option = wrong;

    if (!std::randomize(access_option) with { access_option dist
      {sequential_access := 3, concurrent_access := 7 }; })
      `uvm_fatal(`gfn, "Randomization Failure")

    case (access_option)
      sequential_access: begin // Sequential accesses
        random_access_flash_status();
        super.spi_host_xfer_flash_item(op, payload_size, addr, wait_on_busy);
      end
      concurrent_access: begin // Concurrent accesses
        fork
          begin
            bit send_write, write_sent;

            while (spi_command_finished==0) begin
              randcase
                9: delay_free = 0;
                1: delay_free = 1;
              endcase

              if (!delay_free)
                random_cycle_delay();

              if (!write_sent) begin
                // Only randomize until we send the first write
                if(!std::randomize(send_write) with { send_write dist {1 := 15, 0 := 85}; })
                  `uvm_fatal(`gfn, "Randomization Failure")
              end
              // Sending 1-write only
              if (!write_sent && send_write) begin
                random_access_flash_status(.write(send_write));
                write_sent = 1;
              end
              else begin
                random_access_flash_status(.write(0));
              end
            end // while (spi_command_finished==0)
          end
          begin
            // Thread gets killed on the SPI command below completing
            super.spi_host_xfer_flash_item(op, payload_size, addr, wait_on_busy);
            spi_command_finished = 1;
          end
        join

      end // case: concurrent_access
      two_writes: begin
        // keep reading flash_status, and if the busy bit was set, then we send two writes
        // to flash_status, the first setting the upper bits, and the second clearing the
        // WEL/BUSY bits
        fork
          begin
            bit [TL_DW-1:0] read_status;
            bit [21:0]      other_status;

            while (spi_command_finished==0) begin
              randcase
                9: delay_free = 0;
                1: delay_free = 1;
              endcase

              if (!delay_free)
                random_cycle_delay();

              // Keep reading until the busy bit is set
              if (read_status[0] == 0)
                csr_rd(ral.flash_status, read_status);
              else begin
                // Busy bit is set set - setting first the upper bits of flash_status:
                other_status = $urandom();
                random_access_flash_status(.write(1), .busy(1), .wel(1),
                                           .other_status(other_status));
                cfg.clk_rst_vif.wait_clks($urandom_range(1,5));

                // Clearing busy and wel bits
                random_access_flash_status(.write(1), .busy(0), .wel(0),
                                           .other_status(other_status));
                read_status[0] = 0; // Busy bit has been cleared
              end
            end // forever begin
          end
          begin
            // Thread gets killed on the SPI command below completing
            super.spi_host_xfer_flash_item(op, payload_size, addr, wait_on_busy);
            spi_command_finished = 1;
          end
        join
      end // case: two_writes
      default: `uvm_fatal(`gfn, "Wrong case statement")
    endcase
  endtask

endclass : spi_device_intercept_vseq
