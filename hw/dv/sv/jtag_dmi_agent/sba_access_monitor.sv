// Copyright lowRISC contributors (OpenTitan project).
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
class sba_access_monitor #(type ITEM_T = sba_access_item) extends dv_reactive_monitor #(
    .ITEM_T (ITEM_T),
    .CFG_T  (jtag_agent_cfg));
  `uvm_component_param_utils(sba_access_monitor #(ITEM_T))

  // A handle to the JTAG DMI RAL model. Please set this handle as soon as the instance is created.
  jtag_dmi_reg_block jtag_dmi_ral;
  uvm_reg_addr_t sba_addrs[$];

  // A callback object that's used to augment field predictions
  direct_predict_cb m_predict_cb;

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
    m_predict_cb = new("m_predict_cb");

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
      sba_addrs.push_back(jtag_dmi_ral.sbdata3.get_address());
    end
    `uvm_info(`gfn, $sformatf("sba_addrs: %0p", sba_addrs), UVM_LOW)
  endfunction

  function void connect_phase(uvm_phase phase);
    // Attach m_predict_cb to every field in the three SBA registers (sbcs, sbaddress0-3, sbdata0-3)
    // in jtag_dmi_ral
    uvm_reg sb_regs[$] = '{jtag_dmi_ral.sbcs,
                           jtag_dmi_ral.sbaddress0, jtag_dmi_ral.sbaddress1,
                           jtag_dmi_ral.sbaddress2, jtag_dmi_ral.sbaddress3,
                           jtag_dmi_ral.sbdata0, jtag_dmi_ral.sbdata1,
                           jtag_dmi_ral.sbdata2, jtag_dmi_ral.sbdata3};

    super.connect_phase(phase);

    foreach (sb_regs[i]) begin
      uvm_reg_field fields[$];
      sb_regs[i].get_fields(fields);
      foreach (fields[j]) begin
        uvm_reg_field_cb::add(fields[j], m_predict_cb);
      end
    end
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

  virtual protected task collect_trans();
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
        if (process_sba_csr_read(csr, dmi_item)) begin
          if (!csr.predict(.value(dmi_item.rdata), .kind(UVM_PREDICT_READ))) begin
            `uvm_fatal(get_full_name(),
                       $sformatf("Failed to predict after read from %0s", csr.get_name()))
          end
        end
      end
      else if (dmi_item.req_op == DmiOpWrite) begin
        if (!csr.predict(.value(dmi_item.wdata), .kind(UVM_PREDICT_WRITE))) begin
            `uvm_fatal(get_full_name(),
                       $sformatf("Failed to predict after write to %0s", csr.get_name()))
        end
        process_sba_csr_write(csr);
      end
    end
  endtask

  // Predict what is expected to happen if one of the SBA registers is read.
  //
  // If the sbcs register is read, and sbbusy bit drops on a pending write, we consider the
  // transaction to have completed - we write the predicted SBA transaction to the analysis port.
  //
  // Returns a bit to the caller indicating whether to predict the CSR read or not.
  virtual protected function bit process_sba_csr_read(uvm_reg csr, jtag_dmi_item dmi_item);
    uvm_reg_data_t readondata  = m_predict_cb.get_prediction(jtag_dmi_ral.sbcs.sbreadondata);
    uvm_reg_data_t readonaddr  = m_predict_cb.get_prediction(jtag_dmi_ral.sbcs.sbreadonaddr);
    uvm_reg_data_t sbbusy      = m_predict_cb.get_prediction(jtag_dmi_ral.sbcs.sbbusy);
    uvm_reg_data_t sbbusyerror = m_predict_cb.get_prediction(jtag_dmi_ral.sbcs.sbbusyerror);
    uvm_reg_data_t sberror     = m_predict_cb.get_prediction(jtag_dmi_ral.sbcs.sberror);
    bit do_predict = 1;

    case (csr.get_name())
      "sbcs": begin
        // Update the status bits from transaction item.
        sbbusy      = get_field_val(jtag_dmi_ral.sbcs.sbbusy, dmi_item.rdata);
        sbbusyerror = get_field_val(jtag_dmi_ral.sbcs.sbbusyerror, dmi_item.rdata);
        sberror     = get_field_val(jtag_dmi_ral.sbcs.sberror, dmi_item.rdata);

        // We should have predicted an SBA access if any of the status bits got set.
        if (sbbusy || sbbusyerror) begin
          `DV_CHECK(sba_req_q.size(),
                    $sformatf({"One of these bits is set, but no SBA access was predicted: ",
                               "sbbusy=%0b, sbbusyerror=%0b"}, sbbusy, sbbusyerror))
        end

        // Reflect any mirrored busy error in the pending SBA request
        if (sbbusyerror) sba_req_q[0].is_busy_err = 1'b1;

        if (sba_req_q.size()) begin
          if (sberror) sba_req_q[0].is_err = sba_access_err_e'(sberror);
          if (!sbbusy) begin
            // Write the predicted SBA write transaction to the analysis port.
            if (sba_req_q[0].bus_op == BusOpWrite) begin
              analysis_port.write(sba_req_q.pop_front());
              predict_autoincr_sba_addr();
            end
          end
        end
      end
      "sbaddress0": begin
        uvm_reg_data_t exp_addr = m_predict_cb.get_prediction(jtag_dmi_ral.sbaddress0.address);
        uvm_reg_data_t autoinc = m_predict_cb.get_prediction(jtag_dmi_ral.sbcs.sbautoincrement);
        if (autoinc) begin
          uvm_reg_data_t raw_size = m_predict_cb.get_prediction(jtag_dmi_ral.sbcs.sbaccess);
          sba_access_size_e size = sba_access_size_e'(raw_size);
          // Depending on when the sbaddress0 is read, the predicted sbaddress0 value could be off
          // (less than) the observed by at most 1 increment value.
          `DV_CHECK(dmi_item.rdata inside {exp_addr, exp_addr + (1 << size)})
          // Skip updating the mirrored value (at the call site) since we predict the addr
          // separately.
          do_predict = 0;
        end else begin
          `DV_CHECK_EQ(dmi_item.rdata, exp_addr)
        end
      end
      "sbdata0": begin
        // `DV_CHECK_EQ(dmi_item.rdata, jtag_dmi_ral.sbdata0.get_mirrored_value())
        // If SBA read access completed, then return the data read from this register. We count
        // on stimulus to have read the sbcs register before to ensure the access actually
        // completed. The external scoreboard is expected to verify the correctness of externally
        // indicated errors SbaErrTimeout, SbaErrBadAddr and SbaErrOther, when the stimulus reads
        // the sbcs register during a pending SBA read transaction.
        //
        // The stimulus (in jtag_rv_debugger:sba_access()) terminates the SBA access after
        // reading sbdata0 on read transactions.
        if (sba_req_q.size()) begin
          if (sba_req_q[0].bus_op == BusOpRead && !sbbusy) begin
            sba_req_q[0].rdata[0] = dmi_item.rdata;
            analysis_port.write(sba_req_q.pop_front());
            predict_autoincr_sba_addr();
          end
        end
        // If readondata is set, then a read to this register will trigger a new SBA read.
        if (readondata) begin
          void'(predict_sba_req(BusOpRead));
        end
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("Read to SBA CSR %0s is unsupported", csr.`gfn))
      end
    endcase
    return do_predict;
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
        `uvm_fatal(`gfn, $sformatf("Write to SBA CSR %0s is unsupported", csr.`gfn))
      end
    endcase
  endfunction

  virtual task monitor_ready_to_end();
    forever begin
      if (!sba_req_q.size()) begin
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
      if (cfg.in_reset) begin
        sba_req_q.delete();
        m_predict_cb.on_reset();
      end
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
    uvm_reg_addr_t addr = m_predict_cb.get_prediction(jtag_dmi_ral.sbaddress0.address);
    uvm_reg_data_t data = m_predict_cb.get_prediction(jtag_dmi_ral.sbdata0.data);

    uvm_reg_data_t raw_size = m_predict_cb.get_prediction(jtag_dmi_ral.sbcs.sbaccess);
    sba_access_size_e size  = sba_access_size_e'(raw_size);
    int unsigned size_bytes = 1 << int'(size);

    sba_access_item item;

    // Is the address aligned?
    if (addr << ($bits(addr) - size)) begin
      m_predict_cb.make_direct_prediction(jtag_dmi_ral.sbcs.sberror, SbaErrBadAlignment);
      return 0;
    end

    // This transfer size is only supported if it will fit on the bus. If not, the agent should drop
    // the request and report the bad size through its register interface.
    if (size_bytes > bus_params_pkg::BUS_DBW) begin
      m_predict_cb.make_direct_prediction(jtag_dmi_ral.sbcs.sberror, SbaErrBadSize);
      return 0;
    end

    // Is there already a pending transaction?
    if (m_predict_cb.get_prediction(jtag_dmi_ral.sbcs.sbbusy)) begin
      m_predict_cb.make_direct_prediction(jtag_dmi_ral.sbcs.sbbusyerror, 1);
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
    m_predict_cb.make_direct_prediction(jtag_dmi_ral.sbcs.sbbusy, 1);
    return 1;
  endfunction

  // If autoincr is set then predict the new address. Invoked after the successful completion of
  // previous transfer.
  virtual function void predict_autoincr_sba_addr();
    if (m_predict_cb.get_prediction(jtag_dmi_ral.sbcs.sbautoincrement)) begin
      uvm_reg_data_t raw_size = m_predict_cb.get_prediction(jtag_dmi_ral.sbcs.sbaccess);
      sba_access_size_e size = sba_access_size_e'(raw_size);
      uvm_reg_data_t addr = m_predict_cb.get_prediction(jtag_dmi_ral.sbaddress0.address);

      m_predict_cb.make_direct_prediction(jtag_dmi_ral.sbaddress0.address, addr + (1 << size));
      `uvm_info(`gfn,
                $sformatf("Predicted sbaddr after autoincr: 0x%0h -> 0x%0h",
                          addr, m_predict_cb.get_prediction(jtag_dmi_ral.sbaddress0.address)),
                UVM_HIGH)
    end
  endfunction

endclass
