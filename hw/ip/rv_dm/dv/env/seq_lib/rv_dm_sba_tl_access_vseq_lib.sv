// Copyright lowRISC contributors.
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
  rand bit bad_access;
  rand bit autoincr;
  rand uint autoincr_length;

  constraint autoincr_length_c {
    autoincr_length dist { [0:24] :/ 4, [25:50] :/ 4, [51:200] :/ 2};
  }

  // Base class only does legal accesses.
  constraint bad_access_c {
    bad_access == 0;
  }

  // Base class only does single accesses.
  constraint autoincr_c {
    autoincr == 0;
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

  constraint d_error_pct_c {
    d_error_pct inside {[0:100]};
    d_error_pct dist { 0 :/ 6, [1:20] :/ 2, [21:99] :/ 1, 100 :/ 1};
  }

  constraint d_chan_intg_err_pct_c {
    d_chan_intg_err_pct inside {[0:100]};
    d_chan_intg_err_pct dist { 0 :/ 7, [1:20] :/ 2, [21:100] :/ 1};
  }

  // TODO: Randomize these controls every num_times iteration.
  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }
  constraint unavailable_c {
    unavailable == 0;
  }

  constraint num_trans_c {
    num_trans inside {[20:100]};
  }

  constraint num_times_c {
    num_times inside {[1:5]};
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
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(autoincr)
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(bad_access)
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(read_addr_after_write)
        randomize_req(req);
        `uvm_info(`gfn, $sformatf("Starting transaction %0d/%0d: %0s",
                                  j, num_trans, req.sprint(uvm_default_line_printer)), UVM_MEDIUM)
        sba_access(.jtag_dmi_ral(jtag_dmi_ral), .cfg(cfg.m_jtag_agent_cfg), .req(req));
        `DV_CHECK(!req.is_busy_err)
        `DV_CHECK(!req.timed_out)

        if (bad_access) begin
          `DV_CHECK(req.is_err)
          continue;
        end

        if (autoincr) begin
          logic [BUS_DW-1:0] rwdata;
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(autoincr_length)
          if (req.bus_op == BusOpWrite) begin
            repeat (autoincr_length) begin
              logic is_busy;
              `DV_CHECK_STD_RANDOMIZE_FATAL(rwdata)
              if (!cfg.m_jtag_agent_cfg.in_reset) begin
                csr_wr(.ptr(jtag_dmi_ral.sbdata0), .value(rwdata), .predict(1));
              end
              sba_access_busy_wait_wrap(req);
              if (!$urandom_range(0, 3)) begin  //25%
                csr_rd(.ptr(jtag_dmi_ral.sbaddress0), .value(rwdata));
              end
            end
          end else begin
            if (req.readondata) begin
              sba_access_busy_wait_wrap(req);
              repeat (autoincr_length) begin
                logic is_busy;
                if (!cfg.m_jtag_agent_cfg.in_reset) begin
                  csr_rd(.ptr(jtag_dmi_ral.sbdata0), .value(rwdata));
                end
                sba_access_busy_wait_wrap(req);
                if (!$urandom_range(0, 3)) begin  //25%
                  csr_rd(.ptr(jtag_dmi_ral.sbaddress0), .value(rwdata));
                end
              end
            end
          end
        end

        // If readondata is set, then the read on sbdata0 performed by sba_access invocation
        // above will trigger another SBA read. So we set readondata to 0 and do a busywait.
        if (req.bus_op == BusOpRead && req.readondata) begin
          bit is_busy;
          uvm_reg_data_t rwdata = jtag_dmi_ral.sbcs.get_mirrored_value();
          rwdata = get_csr_val_with_updated_field(jtag_dmi_ral.sbcs.sbreadondata, rwdata, 0);
          csr_wr(.ptr(jtag_dmi_ral.sbcs), .value(rwdata), .predict(1));
          sba_access_busy_wait_wrap(req);
          csr_rd(.ptr(jtag_dmi_ral.sbdata0), .value(rwdata));
        end
      end
      sba_tl_device_seq_stop();
    end
  endtask : body

  // Randomizes legal, valid requests.
  virtual function void randomize_req(sba_access_item req);
    req.disable_rsp_randomization();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        autoincrement == local::autoincr;
        if (bad_access) {
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
    // Since we override the addr, size & bus_op, the original bad_access value may need to be
    // updated.
    bad_access = (req.size > SbaAccessSize32b) || ((req.addr % (1 << req.size)) != 0);
  endfunction

  // Wrapper task for busy wait.
  task sba_access_busy_wait_wrap(sba_access_item req);
    logic is_busy;
    sba_access_busy_wait(jtag_dmi_ral, cfg.m_jtag_agent_cfg, req, is_busy);
    `DV_CHECK(!req.is_err)
    `DV_CHECK(!req.is_busy_err)
    `DV_CHECK(!req.timed_out)
  endtask

endclass

// Drive random traffic out the SBA TL interface with more weightage on accesses that will result
// in sberror begin flagged.
class rv_dm_bad_sba_tl_access_vseq extends rv_dm_sba_tl_access_vseq;
  `uvm_object_utils(rv_dm_bad_sba_tl_access_vseq)
  `uvm_object_new

  constraint bad_access_c {
    bad_access dist {0 :/ 3, 1 :/ 7};
  }

endclass

// Enable address autoincrements on reads and writes. Also ocassionally send bad accesses.
class rv_dm_autoincr_sba_tl_access_vseq extends rv_dm_sba_tl_access_vseq;
  `uvm_object_utils(rv_dm_autoincr_sba_tl_access_vseq)
  `uvm_object_new

  constraint bad_access_c {
    bad_access dist {0 :/ 7, 1 :/ 3};
  }

  constraint autoincr_c {
    autoincr dist {0 :/ 4, 1 :/ 6};
  }

endclass
