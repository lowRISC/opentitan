// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Captures reads and writes to DMI SBA registers to infer transactions on the SBA interface.
//
// Unlike the name suggests, this monitor does not actually monitor the SBA interface
// directly, but indirectly by snooping the reads and writes to the SBA registers in the JTAG DMI
// register space. These are defined in the RISCV debug spec 0.13.2.
//
// From the series of reads and writes to the SBA registers in the JTAG DMI address space, this
// monitor infers accesses over the SBA and writes such predicted accesses to the analysis ports for
// higher level testbench components to process.
//
// Reads and writes made to non SBA registers are passed on through non_sba_jtag_dmi_analysis_port.
class sba_access_monitor #(type ITEM_T = sba_access_item) extends dv_base_monitor#(
    .ITEM_T (ITEM_T),
    .CFG_T  (jtag_agent_cfg));
  `uvm_component_param_utils(sba_access_monitor #(ITEM_T))

  // A handle to the JTAG DMI RAL model. Please set this handle as soon as the instance is created.
  jtag_dmi_reg_block jtag_dmi_ral;
  uvm_reg_addr_t sba_addrs[$];

  // Enables the monitor.
  bit enable;

  // A queue holding pending, unserviced SBA request.
  ITEM_T sba_req_q[$];

  // Incoming (inferred) JTAG DMI transactions.
  uvm_tlm_analysis_fifo #(jtag_dmi_item) jtag_dmi_fifo;

  // Outgoing filtered JTAG DMI transactions that do not touch the SBA registers.
  uvm_analysis_port #(jtag_dmi_item) non_sba_jtag_dmi_analysis_port;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    jtag_dmi_fifo = new("jtag_dmi_fifo", this);
    non_sba_jtag_dmi_analysis_port = new("non_sba_jtag_dmi_analysis_port", this);
    sba_addrs.push_back(jtag_dmi_ral.sbcs.get_address());
    sba_addrs.push_back(jtag_dmi_ral.sbaddress0.get_address());
    if (jtag_dmi_ral.sbcs.sbasize.get_reset() > 32) begin
      sba_addrs.push_back(jtag_dmi_ral.sbaddress1.get_address());
    end
    if (jtag_dmi_ral.sbcs.sbasize.get_reset() > 64) begin
      sba_addrs.push_back(jtag_dmi_ral.sbaddress2.get_address());
    end
    if (jtag_dmi_ral.sbcs.sbasize.get_reset() > 96) begin
      sba_addrs.push_back(jtag_dmi_ral.sbaddress3.get_address());
    end
    sba_addrs.push_back(jtag_dmi_ral.sbdata0.get_address());
    if (jtag_dmi_ral.sbcs.sbaccess64.get_reset()) begin
      sba_addrs.push_back(jtag_dmi_ral.sbdata1.get_address());
    end
    if (jtag_dmi_ral.sbcs.sbaccess128.get_reset()) begin
      sba_addrs.push_back(jtag_dmi_ral.sbdata2.get_address());
    end
    if (jtag_dmi_ral.sbcs.sbaccess128.get_reset()) begin
      sba_addrs.push_back(jtag_dmi_ral.sbdata3.get_address());
    end
    `uvm_info(`gfn, $sformatf("sba_addrs: %0p", sba_addrs), UVM_LOW)
  endfunction

  task run_phase(uvm_phase phase);
    fork
      super.run_phase(phase);
      monitor_reset();
    join
  endtask

  virtual function void report_phase(uvm_phase phase);
    `DV_EOT_PRINT_Q_CONTENTS(sba_access_item, sba_req_q)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(jtag_dmi_item, jtag_dmi_fifo)
  endfunction

  virtual protected task collect_trans(uvm_phase phase);
    jtag_dmi_item dmi_item;

    forever begin
      bit busy;
      uvm_reg csr;
      jtag_dmi_fifo.get(dmi_item);
      `uvm_info(`gfn, $sformatf("Received jtag DMI item:\n%0s",
                                dmi_item.sprint(uvm_default_line_printer)), UVM_HIGH)

      // Pass through DMI accesses that do not touch the SBA registers.
      if (!(dmi_item.addr inside {sba_addrs})) begin
        non_sba_jtag_dmi_analysis_port.write(dmi_item);
        continue;
      end

      // Pass through unsuccessful accesses.
      if (dmi_item.rsp_op != DmiOpOk) begin
        non_sba_jtag_dmi_analysis_port.write(dmi_item);
        continue;
      end

      csr = jtag_dmi_ral.default_map.get_reg_by_offset(dmi_item.addr);

      if (dmi_item.req_op == DmiOpRead) begin
        process_sba_csr_read(csr, dmi_item);
        void'(csr.predict(.value(dmi_item.rdata), .kind(UVM_PREDICT_READ)));
      end
      else if (dmi_item.req_op == DmiOpWrite) begin
        void'(csr.predict(.value(dmi_item.wdata), .kind(UVM_PREDICT_WRITE)));
        process_sba_csr_write(csr);
      end
    end
  endtask

  // Predict what is expected to happen if one of the SBA registers is read.
  //
  // If the sbcs register is read, and sbbusy bit drops on a pending write, we consider the
  // transaction to have completed - we write the predicted SBA transaction to the analysis port.
  virtual protected function void process_sba_csr_read(uvm_reg csr, jtag_dmi_item dmi_item);
    case (csr.get_name())
      "sbcs": begin
        uvm_reg_data_t sbbusy       = get_field_val(jtag_dmi_ral.sbcs.sbbusy, dmi_item.rdata);
        uvm_reg_data_t sbbusyerror  = get_field_val(jtag_dmi_ral.sbcs.sbbusyerror, dmi_item.rdata);
        uvm_reg_data_t sberror      = get_field_val(jtag_dmi_ral.sbcs.sberror, dmi_item.rdata);

        // We should have predicted an SBA access if any of the status bits got set.
        if (sbbusy || sbbusyerror) begin
          `DV_CHECK(sba_req_q.size(),
                    $sformatf({"One of these bits is set, but no SBA access was predicted: ",
                               "sbbusy=%0b, sbbusyerror=%0b"}, sbbusy, sbbusyerror))
        end

        // Check if we correctly predicted busy error.
        `DV_CHECK_EQ(sbbusyerror, jtag_dmi_ral.sbcs.sbbusyerror.get_mirrored_value())
        if (sbbusyerror) sba_req_q[0].is_busy_err = 1'b1;

        // Check if we correctly predicted the malformed SBA access request errors.
        //
        // We can only predict SbaErrBadAlignment and SbaErrBadSize errors. For the externally
        // indicated errors SbaErrTimeout, SbaErrBadAddr and SbaErrOther, we pass the actually seen
        // sberror to the sba_access_item that is written to the analysis port. The external entity
        // reading from this port is expected to verify the correctness of these errors.
        if (sberror inside {SbaErrNone, SbaErrBadAlignment, SbaErrBadSize}) begin
          `DV_CHECK_EQ(sberror, jtag_dmi_ral.sbcs.sberror.get_mirrored_value())
        end

        if (sba_req_q.size() > 0) begin
          if (sberror) sba_req_q[0].is_err = sba_access_err_e'(sberror);
          if (!sbbusy) begin
            // Write the predicted SBA transaction to the analysis port when sbbusy de-asserts in
            // the following scenarios - a bus write, a bus read when readondata is set.
            if (sba_req_q[0].bus_op == BusOpWrite ||
                (sba_req_q[0].bus_op == BusOpRead && `gmv(jtag_dmi_ral.sbcs.sbreadondata))) begin
              ITEM_T tr = sba_req_q.pop_front();
              analysis_port.write(tr);
              predict_autoincr_sba_addr();
            end
          end
        end
      end
      "sbaddress0": begin
        `DV_CHECK_EQ(dmi_item.rdata, jtag_dmi_ral.sbaddress0.get_mirrored_value())
      end
      "sbdata0": begin
        // `DV_CHECK_EQ(dmi_item.rdata, jtag_dmi_ral.sbdata0.get_mirrored_value())
        if (sba_req_q.size() > 0) begin
          // If SBA read access completed, then return the data read from this register. We count on
          // stimulus to have read the sbcs register before to ensure the access actually completed.
          // The external scoreboard is expected to verify the correctness of externally indicated
          // errors SbaErrTimeout, SbaErrBadAddr and SbaErrOther, when the stimulus reads the sbcs
          // register during a pending SBA read transaction.
          //
          // The stimulus (in sba_access_utils_pkg::sba_access()) terminates SBA access on sbdata0
          // read when readonaddr is set and readondata is not set. If readondata is set, then
          // accesses terminate at sbcs read. The monitor bases its predictions on this behavior.
          if (sba_req_q[0].bus_op == BusOpRead &&
              !jtag_dmi_ral.sbcs.sbbusy.get_mirrored_value() &&
              (`gmv(jtag_dmi_ral.sbcs.sbreadonaddr) && !`gmv(jtag_dmi_ral.sbcs.sbreadondata))) begin
            ITEM_T tr = sba_req_q.pop_front();
            tr.rdata[0] = dmi_item.rdata;
            analysis_port.write(tr);
          end
        end
        // If readondata is set, then a read to this register will trigger a new SBA read.
        if (jtag_dmi_ral.sbcs.sbreadondata.get_mirrored_value()) begin
          void'(predict_sba_req(BusOpRead));
        end
        void'(csr.predict(.value(dmi_item.rdata), .kind(UVM_PREDICT_READ)));
      end
      default: begin
        `uvm_info(`gfn, $sformatf("Read to SBA CSR %0s is unsupported", csr.`gfn), UVM_LOW)
      end
    endcase
  endfunction

  // Predict what is expected to happen if one of the SBA registers is written.
  virtual protected function void process_sba_csr_write(uvm_reg csr);
    case (csr.get_name())
      "sbcs": begin
        // Nothing to do.
      end
      "sbaddress0": begin
        // If readonaddr is set, then a write to this register will trigger an SBA read.
        if (jtag_dmi_ral.sbcs.sbreadonaddr.get_mirrored_value()) begin
          void'(predict_sba_req(BusOpRead));
        end
      end
      "sbdata0": begin
        // A write to this register will trigger an SBA write.
        void'(predict_sba_req(BusOpWrite));
      end
      default: begin
        `uvm_info(`gfn, $sformatf("Write to SBA CSR %0s is unsupported", csr.`gfn), UVM_LOW)
      end
    endcase
  endfunction

  virtual task monitor_ready_to_end();
    forever begin
      if (sba_req_q.size() == 0) begin
        ok_to_end = 1'b1;
        wait (sba_req_q.size());
      end else begin
        string msg;
        ok_to_end = 1'b0;
        foreach (sba_req_q[i]) begin
        msg = {msg, "\n", $sformatf("  sba_req_q[%0d]: %0s",
                                    i, sba_req_q[i].sprint(uvm_default_line_printer))};
        end
        `uvm_info(`gfn, $sformatf("The following transactions are pending:\n%0s", msg), UVM_LOW)
        wait (sba_req_q.size() == 0);
      end
    end
  endtask

  virtual protected task monitor_reset();
    forever @cfg.in_reset begin
      if (cfg.in_reset) sba_req_q.delete();
    end
  endtask

  // Predicts if an SBA request will be made.
  //
  // It uses the values predicted from writes to the SBA registers that occurred before, to check
  // validity and create a predicted SBA request item. It returns 1 if the SBA access is predicted
  // to be made, else 0. Before returning 1, it records the predicted SBA request.
  //
  // bus_op: the predicted read or write operation.
  // item: The returned expected request predicted to be sent.
  // returns 1 if a new SBA request is expected to be sent, else 0.
  virtual protected function bit predict_sba_req(input bus_op_e bus_op);
    uvm_reg_addr_t addr = jtag_dmi_ral.sbaddress0.get_mirrored_value();
    uvm_reg_data_t data = jtag_dmi_ral.sbdata0.get_mirrored_value();
    sba_access_size_e size = sba_access_size_e'(jtag_dmi_ral.sbcs.sbaccess.get_mirrored_value());
    sba_access_item item;

    // Is the address aligned?
    if (addr << ($bits(addr) - size)) begin
      void'(jtag_dmi_ral.sbcs.sberror.predict(.value(SbaErrBadAlignment),
                                              .kind(UVM_PREDICT_DIRECT)));
      return 0;
    end

    // Is the transfer size supported?
    if (size > $clog2(bus_params_pkg::BUS_DBW)) begin
      void'(jtag_dmi_ral.sbcs.sberror.predict(.value(SbaErrBadSize), .kind(UVM_PREDICT_DIRECT)));
      return 0;
    end

    // Is there already a pending transaction?
    if (jtag_dmi_ral.sbcs.sbbusy.get_mirrored_value()) begin
      void'(jtag_dmi_ral.sbcs.sbbusyerror.predict(.value(1), .kind(UVM_PREDICT_DIRECT)));
      return 0;
    end

    item = ITEM_T::type_id::create("item");
    item.bus_op = bus_op;
    item.addr = addr;
    item.size = size;
    item.is_err = SbaErrNone;
    item.is_busy_err = 0;
    item.timed_out = 0;
    if (bus_op == BusOpWrite) item.wdata[0] = data;
    `uvm_info(`gfn, $sformatf("Predicted new SBA req: %0s",
                              item.sprint(uvm_default_line_printer)), UVM_MEDIUM)
    `DV_CHECK_EQ(sba_req_q.size(), 0,
                 $sformatf("Predicted new SBA req before previous req %0s was popped.",
                           sba_req_q[$].sprint(uvm_default_line_printer)))
    sba_req_q.push_back(item);
    req_analysis_port.write(item);
    void'(jtag_dmi_ral.sbcs.sbbusy.predict(.value(1), .kind(UVM_PREDICT_DIRECT)));
    return 1;
  endfunction

  // If autoincr is set then predict the new address. Invoked after the successful completion of
  // previous transfer.
  virtual function void predict_autoincr_sba_addr();
    if (jtag_dmi_ral.sbcs.sbautoincrement.get_mirrored_value()) begin
      sba_access_size_e size = sba_access_size_e'(jtag_dmi_ral.sbcs.sbaccess.get_mirrored_value());
      uvm_reg_data_t addr = jtag_dmi_ral.sbaddress0.get_mirrored_value();
      void'(jtag_dmi_ral.sbaddress0.predict(.value(addr + (1 << size)),
                                            .kind(UVM_PREDICT_DIRECT)));
    end
  endfunction

endclass
