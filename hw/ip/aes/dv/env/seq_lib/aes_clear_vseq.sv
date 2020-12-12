// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will send a number of messages
// and in each case it will try to reset one or more
// registers in the DUT verifying that registers are
// indeed reset and false values are not posted anywhere
// and more importantly that parts of the Key and IV are not exposed

// the first part Runs in auto mode
// where the DUT recognized when to start an operation
// the second part is done in manual mode
// where special cases are setup before the start is triggered.


class aes_clear_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_clear_vseq)
  `uvm_object_new

  aes_message_item my_message;
  aes_seq_item     nxt_item   = new();
  aes_seq_item     last_item  = new();
  clear_t          clr_mask   = '1;
  bit [31:0]       status;

  task body();
    `uvm_info(`gfn, $sformatf("\n\n\t ----| STARTING AES CLEAR SEQUENCE |----\n %s",
                    cfg.convert2string()), UVM_LOW)

    // generate list of messages //
    generate_message_queue();

    // process all messages //
    while (message_queue.size() > 0) begin
      // get next message from queue
      my_message = new();
      my_message = message_queue.pop_back();

      // for this message generate configuration
      // and data items (split message into blocks)
      generate_aes_item_queue(my_message);

      // setup and transmit based on settings
      nxt_item = aes_item_queue.pop_back();
      setup_dut(nxt_item);

      // data and config are not in same
      // items so both are needed for this.
      last_item = nxt_item;
      nxt_item = aes_item_queue.pop_back();
      write_data_key_iv(last_item, nxt_item.data_in);
      if (my_message.manual_operation) begin
        // in manual mode we can start an operation
        // regardless of the register states
        trigger();

      end else begin
        // if a register was cleared
        // re write the data to have the DUT move on
        // re-clear to remove anything that was written after the
        // first clearing - to avoid DUT starting prematurely
        `uvm_info(`gfn, $sformatf("\n\t polling for Idle"), UVM_LOW)
        clr_mask.data_out = 0;
        // read status to see if DUT is in operation
        csr_rd(.ptr(ral.status), .value(status));
        // if not in operation re-wrte cleared values
        if(status[0] && |(last_item.clear_reg & clr_mask)) begin
          clear_regs(last_item.clear_reg);
          if (last_item.clear_reg.data_in) begin
            csr_spinwait(.ptr(ral.status.idle) , .exp_data(1'b1));
            `uvm_info(`gfn, $sformatf("\n\t ----| Re-Adding cleared data "), UVM_LOW)
            add_data(nxt_item.data_in, nxt_item.do_b2b);
          end

          if (last_item.clear_reg.iv) begin
            csr_spinwait(.ptr(ral.status.idle) , .exp_data(1'b1));
            `uvm_info(`gfn, $sformatf("\n\t ----| Re-Adding cleared IV "), UVM_LOW)
            write_iv(last_item.iv, last_item.do_b2b);
          end

          if (last_item.clear_reg.key) begin
            csr_spinwait(.ptr(ral.status.idle) , .exp_data(1'b1));
            `uvm_info(`gfn, $sformatf("\n\t ----| Re-Adding cleared key "), UVM_LOW)
            write_key(last_item.key, last_item.do_b2b);
          end
        end
      end

      if (nxt_item.mode != AES_NONE) begin
        // if data out was not cleared
        // wait for data out ready
        // else poll a few times to
        // see if data out is produced
        // the case where data out was cleared before
        // starting operation if not just add data
        // and continue
        if (!last_item.clear_reg.data_out) begin
          csr_spinwait(.ptr(ral.status.output_valid) , .exp_data(1'b1));    // poll for data valid
          read_data(nxt_item.data_out, nxt_item.do_b2b);
        end else begin
           csr_spinwait(.ptr(ral.status.idle) , .exp_data(1'b1));
          repeat(10) begin
            csr_rd(.ptr(ral.status), .value(status));
            if (status[2]) begin
              break;
            end
          end
          read_data(nxt_item.data_out, nxt_item.do_b2b);
        end
      end else begin
        `uvm_fatal(`gfn, $sformatf("\n\t ----| Invalid Modes are not supported in this test"))
      end

      // transmit the rest of the message
      `uvm_info(`gfn, $sformatf("\n\t ----| data left in queue %d",aes_item_queue.size()), UVM_LOW)
      while (aes_item_queue.size() > 0) begin
        nxt_item = aes_item_queue.pop_back();
        add_data(nxt_item.data_in, nxt_item.do_b2b);
        if (my_message.manual_operation) trigger();
        if (nxt_item.mode != AES_NONE) begin
          `uvm_info(`gfn, $sformatf("\n\t ----| POLLING FOR DATA"), UVM_DEBUG)
          csr_spinwait(.ptr(ral.status.output_valid) , .exp_data(1'b1));    // poll for data valid
          read_data(nxt_item.data_out, nxt_item.do_b2b);
        end
      end
      `uvm_info(`gfn, $sformatf("\n\t ----| DONE TRANMISTTING MESSAGE"), UVM_LOW)
      // make sure DUT is ready for the next message
      csr_spinwait(.ptr(ral.status.idle) , .exp_data(1'b1));
    end
  endtask : body
endclass
