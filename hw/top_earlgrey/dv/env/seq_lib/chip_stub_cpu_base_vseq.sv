// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this is the base vseq that uses stub mode, this vseq can be extended for these tests
// 1. CSR tests
// 2. IP tests which run in chip-level and send TL items on ibex output
class chip_stub_cpu_base_vseq extends chip_base_vseq;
  `uvm_object_utils(chip_stub_cpu_base_vseq)

  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    // Deselect JTAG interface.
    if (cfg.jtag_riscv_map != null) cfg.tap_straps_vif.drive(SelectRVJtagTap);
    else                            cfg.tap_straps_vif.drive(DeselectJtagTap);
    enable_asserts_in_hw_reset_rand_wr = 0;

    // In top-level uart RX pin may be selected in pinmux. CSR tests may randomly enable line
    // loopback, which will connect TX with RX. If RX isn't enabled in pinmux, it will be 0.
    // moniter will start to check the TX data when it changes from 1 to 0. But the length of 0 may
    // be not right in CSR test, which causes a protocal error on TX
    // In block-level, we always tie RX to 1 (idle) in CSR test so that we don't need to disable TX
    // monitor in block-level
    foreach (cfg.m_uart_agent_cfgs[i]) cfg.m_uart_agent_cfgs[i].en_tx_monitor = 0;
  endtask

  task post_start();
    super.post_start();
    // Random CSR rw might trigger alert. Some alerts will conintuously be triggered until reset
    // applied, which will cause alert_monitor phase_ready_to_end timeout.
    apply_reset();
  endtask

  virtual task apply_reset(string kind = "HARD");
    super.apply_reset(kind);
    // Backdoor load the OTP image.
    cfg.mem_bkdr_util_h[Otp].load_mem_from_file(cfg.otp_images[cfg.use_otp_image]);

    // internal reset does not immediately go to 0 when external reset is applied
    wait (cfg.rst_n_mon_vif.pins[0] === 0);
    wait (cfg.rst_n_mon_vif.pins[0] === 1);

  endtask

  virtual task dut_init(string reset_kind = "HARD");
    // make sure jtag rst triggers
    cfg.tap_straps_vif.drive(SelectRVJtagTap);
    super.dut_init(reset_kind);
    if (cfg.jtag_riscv_map == null) cfg.tap_straps_vif.drive(DeselectJtagTap);
  endtask

endclass

`undef add_ip_csr_exclusions
