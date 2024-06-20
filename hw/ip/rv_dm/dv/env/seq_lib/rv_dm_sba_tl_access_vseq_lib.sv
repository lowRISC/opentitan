// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Initiate random traffic on the SBA TL interface via JTAG.
//
// The base class does *everything*, in terms of covering the SBA access state space. However, the
// knobs to initiate "bad" SBA accesses and enable address auto-increment are turned off. They are
// enabled in extended sequences instead.
//
// While these set of sequences perform some basic checks, *all* of the necessary checks are split
// between sba_access_monitor and the rv_dm_scoreboard. The former does SBA access related checks
// (such as predicting sberror / sbbusyerror, autoincremented address, predicting when an SBA access
// will be made etc.) The latter (scoreboard) performs end-to-end checks, ensuring the SBA accesses
// predicted by the sba_access_monitor is correctly showing up on the SBA TL interface.
class rv_dm_sba_tl_access_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_sba_tl_access_vseq)
  `uvm_object_new

  rand int min_rsp_delay;
  rand int max_rsp_delay;
  rand int d_error_pct;
  rand int d_chan_intg_err_pct;

  rand int num_times;
  rand sba_access_item req;
  rand bit bad_req;
  rand uint autoincrement;

  // Base class only does legal accesses.
  constraint bad_req_c {
    bad_req == 0;
  }

  // Base class only does single accesses.
  constraint autoincrement_c {
    autoincrement == 0;
  }

  // To generate reads to the same addr followed by previous writes.
  rand bit read_addr_after_write;
  bus_op_e          bus_op_prev;
  bit [BUS_AW-1:0]  addr_prev;
  sba_access_size_e size_prev;

  constraint min_rsp_delay_c {
    cfg.zero_delays -> min_rsp_delay == 0;
    min_rsp_delay inside {[0:10]};
  }

  constraint max_rsp_delay_c {
    solve min_rsp_delay before max_rsp_delay;
    cfg.zero_delays -> max_rsp_delay == 0;
    max_rsp_delay >= min_rsp_delay;
    max_rsp_delay inside {[min_rsp_delay:min_rsp_delay+100]};
  }

  // Base class does not set d_error=1 on SBA TL responses.
  constraint d_error_pct_c {
    d_error_pct == 0;
  }

  // Base class does not inject TL intg error on SBA TL responses.
  constraint d_chan_intg_err_pct_c {
    d_chan_intg_err_pct == 0;
  }

  // TODO: Randomize these controls every num_times iteration.
  constraint unavailable_c {
    unavailable == 0;
  }

  constraint num_trans_c {
    num_trans inside {[10:20]};
  }

  constraint num_times_c {
    num_times inside {[1:2]};
  }

  constraint read_addr_after_write_c {
    read_addr_after_write dist {0 :/ 7, 1 :/ 3};
  }

  task body();
    num_times.rand_mode(0);

    // TODO: Fix and invoke sba_tl_device_seq_disable_tlul_assert_host_sba_resp_svas() instead.
    cfg.rv_dm_vif.disable_tlul_assert_host_sba_resp_svas = 1'b1;

    sba_tl_device_seq_stop();
    for (int i = 1; i <= num_times; i++) begin
      `uvm_info(`gfn, $sformatf("Starting iteration %0d/%0d", i, num_times), UVM_MEDIUM)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_trans)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(min_rsp_delay)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(max_rsp_delay)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(d_error_pct)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(d_chan_intg_err_pct)
      sba_tl_device_seq_start(.min_rsp_delay(min_rsp_delay),
                              .max_rsp_delay(max_rsp_delay),
                              .d_error_pct(d_error_pct),
                              .d_chan_intg_err_pct(d_chan_intg_err_pct));
      num_trans.rand_mode(0);
      for (int j = 1; j <= num_trans; j++) begin
        req = sba_access_item::type_id::create("req");
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(autoincrement)
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(bad_req)
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(read_addr_after_write)
        randomize_req(req);
        `uvm_info(`gfn, $sformatf("Starting %s transaction %0d/%0d: %0s",
                                  bad_req ? "bad" : "good",
                                  j, num_trans, req.sprint(uvm_default_line_printer)), UVM_MEDIUM)
        cfg.debugger.sba_access(req);
        `DV_CHECK(!req.timed_out)
        `DV_CHECK(!req.is_busy_err)
        if (req.bus_op == BusOpRead && !req.readonaddr && !req.readondata) begin
          // No SBA access, so no error reporting.
          `DV_CHECK_EQ(req.is_err, SbaErrNone)
        end else begin
          if (bad_req) begin
            `DV_CHECK(!(req.is_err inside {SbaErrNone, SbaErrTimeout}),
                      $sformatf("Incorrect sberror: %0s", req.sprint(uvm_default_line_printer)))
          end
          if (req.is_err == SbaErrOther) begin
            // TODO: Verify alert fired.
            // Reset the DUT to clear the intg error.
            dut_init();
          end
        end
      end
      sba_tl_device_seq_stop();
    end
  endtask : body

  // Randomizes legal, valid requests.
  virtual function void randomize_req(sba_access_item req);
    req.autoincrement = autoincrement;
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        if (bad_req) {
          // Create unsupported size or unaligned address error cases.
          (size > SbaAccessSize32b) || ((addr % (1 << size)) != 0);
        } else {
          size <= SbaAccessSize32b;
          (addr % (1 << size)) == 0;
        }
    )
    override_req_to_read_addr_after_write(req);
  endfunction

  // Overrides the req after randomization, to read the previously written address.
  virtual function void override_req_to_read_addr_after_write(sba_access_item req);
    if (read_addr_after_write && bus_op_prev == BusOpWrite) begin
      req.bus_op = BusOpRead;
      req.addr = addr_prev;
      req.size = size_prev;
    end
    bus_op_prev = req.bus_op;
    addr_prev = req.addr;
    size_prev = req.size;
    // Since we override the addr, size & bus_op, the original bad_req value may need to be
    // updated.
    bad_req = (req.size > SbaAccessSize32b) || ((req.addr % (1 << req.size)) != 0);
  endfunction

endclass

// Returns responses from the TL side with longer delays to generate sbbusy cases.
class rv_dm_delayed_resp_sba_tl_access_vseq extends rv_dm_sba_tl_access_vseq;
  `uvm_object_utils(rv_dm_delayed_resp_sba_tl_access_vseq)
  `uvm_object_new

  constraint min_rsp_delay_c {
    if (cfg.zero_delays) {
      min_rsp_delay == 0;
    } else {
      min_rsp_delay dist {[10:100] :/ 1, [101:500] :/ 7, [501:2000] :/ 2};
    }
  }

endclass

// Drive random traffic out the SBA TL interface with more weightage on accesses that will result
// in sberror begin flagged, either due to a bad request or a bad response via d_error / d_chan
// intg err.
class rv_dm_bad_sba_tl_access_vseq extends rv_dm_sba_tl_access_vseq;
  `uvm_object_utils(rv_dm_bad_sba_tl_access_vseq)
  `uvm_object_new

  constraint min_rsp_delay_c {
    if (cfg.zero_delays) {
      min_rsp_delay == 0;
    } else {
      min_rsp_delay dist {[0:100] :/ 8, [101:500] :/ 2};
    }
  }

  constraint bad_req_c {
    bad_req dist {0 :/ 6, 1 :/ 4};
  }

  constraint d_error_pct_c {
    d_error_pct dist { 0 :/ 1, [1:20] :/ 3, [21:99] :/ 5, 100 :/ 1 };
  }

  constraint d_chan_intg_err_pct_c {
    d_chan_intg_err_pct dist { 0 :/ 2, [1:20] :/ 3, [21:99] :/ 4, 100 :/ 1 };
  }

endclass

// Enable address autoincrements on reads and writes. Also ocassionally send bad requests and
// responses.
class rv_dm_autoincr_sba_tl_access_vseq extends rv_dm_sba_tl_access_vseq;
  `uvm_object_utils(rv_dm_autoincr_sba_tl_access_vseq)
  `uvm_object_new

  constraint min_rsp_delay_c {
    if (cfg.zero_delays) {
      min_rsp_delay == 0;
    } else {
      min_rsp_delay dist {[0:100] :/ 8, [101:500] :/ 2};
    }
  }

  constraint bad_req_c {
    bad_req dist {0 :/ 7, 1 :/ 3};
  }

  constraint d_error_pct_c {
    d_error_pct dist { 0 :/ 1, [1:20] :/ 3, [21:99] :/ 5, 100 :/ 1 };
  }

  constraint d_chan_intg_err_pct_c {
    d_chan_intg_err_pct dist { 0 :/ 3, [1:20] :/ 3, [21:99] :/ 3, 100 :/ 1 };
  }

  constraint autoincrement_c {
    autoincrement dist { 0 :/ 4, [1:24] :/ 2, [25:50] :/ 2, [51:200] :/ 2};
  }

endclass
