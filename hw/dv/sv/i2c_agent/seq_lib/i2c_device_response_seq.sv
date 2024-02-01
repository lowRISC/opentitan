// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_device_response_seq extends i2c_base_seq;
  `uvm_object_utils(i2c_device_response_seq)
  `uvm_object_new

  REQ w_q[256][$];

  protected virtual task get_dev_req(output REQ req);
    fork
      begin: isolation_thread
        fork
          begin
            REQ item;
            p_sequencer.req_analysis_fifo.get(item);
            `downcast(req, item)
          end
          wait (stop);
        join_any
        #0;
        disable fork;
      end
    join
  endtask

  task send_device_mode_txn();
    // get seq for agent running in Device mode
    fork
      forever begin
        REQ req;
        get_dev_req(req);
        if (req != null) begin
          `uvm_info(`gfn, $sformatf("bus_op:%s drv_type:%s data_q:%p",req.bus_op.name,
                                    req.drv_type.name, req.data_q), UVM_HIGH)
          if (req.bus_op == BusOpWrite && req.drv_type == DevAck && req.data_q.size() > 0) begin
            w_q[req.addr].push_back(req);
          end else if (req.bus_op == BusOpRead && req.drv_type == RdData) begin
            if (w_q[req.addr].size() == 0) begin
              `uvm_fatal(`gfn, $sformatf("Read requested on empty Write queue"))
            end else begin
              rsp = w_q[req.addr].pop_front();
              req.rdata = rsp.wdata;
            end
          end
          start_item(req);
          finish_item(req);
        end
        if (stop) break;
      end // forever begin
      forever begin
        @(negedge cfg.vif.rst_ni);
        foreach (w_q[i]) begin
          w_q[i].delete();
        end
      end
    join
  endtask // send_device_mode

endclass // i2c_device_response_seq
