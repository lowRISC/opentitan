// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Drive random traffic out the SBA TL interface. Scoreboard checks the packet integrity.
class rv_dm_sba_tl_access_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_sba_tl_access_vseq)
  `uvm_object_new

  rand int min_rsp_delay;
  rand int max_rsp_delay;
  rand int d_error_pct;
  rand int d_chan_intg_err_pct;

  rand int num_times;
  rand bus_op_e bus_op;
  rand bit [2:0] size;
  rand bit [BUS_AW-1:0] addr;
  rand bit [BUS_DW-1:0] data;
  rand bit readonaddr;
  rand bit readondata;
  rand bit autoincrement;

  // To generate reads to the same addr followed by previous writes.
  rand bit read_addr_after_write;
  bus_op_e bus_op_prev;
  bit [BUS_AW-1:0] addr_prev;

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
    d_error_pct dist { 0 :/ 6, [1:99] :/ 2, 100 :/ 2};
  }

  constraint d_chan_intg_err_pct_c {
    d_chan_intg_err_pct inside {[0:100]};
    d_chan_intg_err_pct dist { 0 :/ 6, [1:99] :/ 2, 100 :/ 2};
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

  // TODO: The design only supports 32b accesses at the moment.
  constraint size_c {
    size == 2;
  }

  // TODO: Save for later.
  constraint autoincrement_c {
    autoincrement == 0;
  }

  constraint num_trans_c {
    num_trans inside {[20:50]};
  }

  constraint num_times_c {
    num_times inside {[1:5]};
  }

  constraint read_addr_after_write_c {
    read_addr_after_write dist {0 :/ 7, 1 :/ 3};
  }

  function void post_randomize();
    if (read_addr_after_write && bus_op_prev == BusOpWrite) begin
      bus_op = BusOpRead;
      addr = addr_prev;
    end
    bus_op_prev = bus_op;
    addr_prev = addr;
  endfunction

  task body();
    num_times.rand_mode(0);

    // TODO: Fix and invoke sba_tl_device_seq_disable_tlul_assert_host_sba_resp_svas() instead.
    cfg.rv_dm_vif.disable_tlul_assert_host_sba_resp_svas = 1'b1;

    sba_tl_device_seq_stop();
    for (int i = 1; i <= num_times; i++) begin
      `uvm_info(`gfn, $sformatf("Starting iteration %0d/%0d", i, num_times), UVM_LOW)
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
        `DV_CHECK_RANDOMIZE_FATAL(this)
        `uvm_info(`gfn, $sformatf("Starting transaction %0d/%0d", j, num_trans), UVM_LOW)
        sba_access(.jtag_dmi_ral(jtag_dmi_ral),
                   .cfg(cfg.m_jtag_agent_cfg),
                   .bus_op(bus_op),
                   .size(size),
                   .addr(addr),
                   .data(data),
                   .readonaddr(readonaddr),
                   .readondata(readondata),
                   .autoincrement(autoincrement));
      end
      sba_tl_device_seq_stop();
    end
  endtask : body

endclass
