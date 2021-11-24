// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO, only support testing hardened count for now
virtual task run_sec_cm_fi_vseq(int num_times = 1);
  pre_run_sec_cm_fi_vseq();
  for (int trans = 1; trans <= num_times; trans++) begin
    `uvm_info(`gfn, $sformatf("Running run_sec_cm_fi_vseq %0d/%0d", trans, num_times), UVM_LOW)
    test_sec_cm_fi();
  end
  post_run_sec_cm_fi_vseq();
endtask : run_sec_cm_fi_vseq

// callback task for extended class. We can disable assertions in this task
virtual task pre_run_sec_cm_fi_vseq();
endtask : pre_run_sec_cm_fi_vseq

// callback task for extended class
virtual task post_run_sec_cm_fi_vseq();
endtask : post_run_sec_cm_fi_vseq

// User should extend this task to add additional check, such as
// - Check that err_code/fault_status is updated correctly and preserved until reset.
// - Verify any operations that follow fail (as applicable).
// refer to ip/keymgr/dv/env/seq_lib/keymgr_common_vseq.sv as an example
virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
  // TODO, it's better to unify these to one alert
  string sec_cm_alert_name = cfg.tl_intg_alert_name;

  `DV_CHECK_FATAL(sec_cm_alert_name inside {cfg.list_of_alerts},
                  $sformatf("sec_cm_alert_name (%s) is not inside %p",
                            sec_cm_alert_name, cfg.list_of_alerts))

  `uvm_info(`gfn, $sformatf("expected fatal alert is triggered for %s", if_proxy.sec_cm_type.name),
            UVM_LOW)

  // This is a fatal alert and design keeps sending it until reset is issued.
  // Check alerts are triggered for a few times
  repeat (5) begin
    wait_alert_trigger(sec_cm_alert_name, .wait_complete(1));
  end
endtask : check_sec_cm_fi_resp

virtual task test_sec_cm_fi();
  sec_cm_base_if_proxy if_proxy_q[$] = sec_cm_pkg::sec_cm_if_proxy_q;

  if_proxy_q.shuffle();
  while (if_proxy_q.size) begin
    sec_cm_base_if_proxy if_proxy = if_proxy_q.pop_front();

    sec_cm_fi_ctrl_svas(if_proxy, .enable(0));
    sec_cm_inject_fault(if_proxy);

    // Randomly force the cnt to normal value (error will be cleared) to make sure design latches
    // the error
    if ($urandom_range(0, 1)) begin
      sec_cm_restore_fault(if_proxy);
    end

    check_sec_cm_fi_resp(if_proxy);

    sec_cm_fi_ctrl_svas(if_proxy, .enable(1));
    // issue hard reset for fatal alert to recover
    dut_init("HARD");
  end
endtask : test_sec_cm_fi

virtual task sec_cm_inject_fault(sec_cm_base_if_proxy if_proxy);
  if_proxy.inject_fault();
endtask : sec_cm_inject_fault

virtual task sec_cm_restore_fault(sec_cm_base_if_proxy if_proxy);
  if_proxy.restore_fault();
endtask : sec_cm_restore_fault

virtual function void sec_cm_fi_ctrl_svas(sec_cm_base_if_proxy if_proxy, bit enable);
endfunction : sec_cm_fi_ctrl_svas
