// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// JTAG and TL CSR test
class lc_ctrl_jtag_access_vseq extends lc_ctrl_base_vseq;

  // Who should claim the mutex
  rand lc_ctrl_csr_intf_e mutex_owner_write, mutex_owner_read;

  // Randomly assert scan_rst_ni - should have no effect
  // unless scanmode_i == MuBi4True
  rand bit scan_rst_ni;

  // Writable registers gated by transition_regwen
  // verilog_format: off - avoid bad formatting
  const string LcCtrlRWRegs[] = '{
      "transition_ctrl",
      "transition_token_0",
      "transition_token_1",
      "transition_token_2",
      "transition_token_3",
      "transition_target",
      "otp_vendor_test_ctrl"
  };
  // verilog_format: on

  // Read/write access
  typedef struct {
    dv_base_reg r;
    lc_ctrl_csr_intf_e map_sel;
    bit blocking;
  } reg_access_t;
  // Read / write registers controlled by the mutex
  dv_base_reg m_mutex_regs[$];
  // Mutex register
  dv_base_reg m_claim_transition_if;
  // regwen register
  dv_base_reg m_transition_regwen;
  // Acccess maps [LcCtrlTLUL] -> TileLink, [LcCtrlJTAG] -> JTAG
  uvm_reg_map m_map[lc_ctrl_csr_intf_e];
  // Queue of register access specs
  reg_access_t m_reg_accesses[$];

  `uvm_object_utils(lc_ctrl_jtag_access_vseq)
  `uvm_object_new

  constraint num_trans_c {num_trans inside {[1 : 20]};}

  virtual task pre_start();
    uvm_reg rs[$];
    uvm_reg_map maps[$];
    super.pre_start();

    cfg.ral.get_registers(rs);
    while (rs.size()) begin
      dv_base_reg r;
      `downcast(r, rs.pop_front())
      if (r.get_name() inside {LcCtrlRWRegs}) m_mutex_regs.push_back(r);
      if (r.get_name() == "claim_transition_if") m_claim_transition_if = r;
      if (r.get_name() == "transition_regwen") m_transition_regwen = r;
    end

    cfg.ral.get_maps(maps);
    while (maps.size()) begin
      uvm_reg_map m;
      m = maps.pop_front();
      if (m.get_name() == "default_map") m_map[LcCtrlTLUL] = m;
      if (m.get_name() == "jtag_riscv_map") m_map[LcCtrlJTAG] = m;
    end

  endtask

  // Overload this to ensure we don't get scrap state
  // Drive OTP input `lc_state` and `lc_cnt`.
  virtual task drive_otp_i(bit rand_otp_i = 1);
    if (rand_otp_i) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(lc_state, !(lc_state inside {LcStScrap});)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(lc_cnt, (lc_state != LcStRaw) -> (lc_cnt != LcCnt0);)
    end else begin
      lc_state = LcStRaw;
      lc_cnt   = LcCnt0;
    end
    cfg.lc_ctrl_vif.init(lc_state, lc_cnt);
  endtask

  virtual task body();
    int i = 0;

    repeat (num_trans) begin
      i++;
      `uvm_info(`gfn, $sformatf(
                "body: start of iteration %0d mutex_owner_write=%s mutex_owner_read=%s",
                i,
                mutex_owner_write.name(),
                mutex_owner_read.name()
                ), UVM_MEDIUM)

      // set scan_rst_i - should have no effect unless scanmode_i == MuBi4True
      cfg.lc_ctrl_vif.scan_rst_ni = scan_rst_ni;

      create_reg_accesses();
      m_reg_accesses.shuffle();

      // Claim the mutex for the write phase
      csr_write_mutex_claim();

      //
      // Write registers by both interfaces
      // Only expect that the unlocked interface will update the register
      //

      foreach (m_reg_accesses[i]) begin
        const bit Blocking = m_reg_accesses[i].blocking;
        const bit IsUnlocked = (m_reg_accesses[i].map_sel == mutex_owner_write);
        const uvm_reg_map Map = m_map[m_reg_accesses[i].map_sel];
        csr_wr(.ptr(m_reg_accesses[i].r), .value($urandom()), .check(UVM_NO_CHECK), .map(Map),
               .predict(IsUnlocked), .blocking(Blocking));
      end
      csr_utils_pkg::wait_no_outstanding_access();

      create_reg_accesses();
      m_reg_accesses.shuffle();

      // Claim the mutex for the read phase
      csr_read_mutex_claim();

      //
      // Read after writing
      // If we are reading via the unlocked interface we check against the mirrored value
      // Otherwise we expect to read 0
      //
      foreach (m_reg_accesses[i]) begin
        const bit Blocking = m_reg_accesses[i].blocking;
        const bit IsUnlocked = (m_reg_accesses[i].map_sel == mutex_owner_read);
        const uvm_reg_map Map = m_map[m_reg_accesses[i].map_sel];

        csr_rd_check(.ptr(m_reg_accesses[i].r), .compare_vs_ral(IsUnlocked), .map(Map),
                     .blocking(Blocking), .compare_value(0));
      end
      csr_utils_pkg::wait_no_outstanding_access();

      `DV_CHECK_RANDOMIZE_FATAL(this)
    end

  endtask

  // Claim the mutex for the register writes
  virtual task csr_write_mutex_claim;
    lc_ctrl_csr_intf_e not_mutex_owner_write =
        (mutex_owner_write == LcCtrlTLUL) ? LcCtrlJTAG : LcCtrlTLUL;
    `uvm_info(`gfn, $sformatf(
              "csr_write_mutex_claim: claiming mutex for interface %s", mutex_owner_write.name()),
              UVM_MEDIUM)
    // verilog_format: off
    `DV_SPINWAIT(
        fork
          claim_mutex(mutex_owner_write);
          release_mutex(not_mutex_owner_write);
        join
        )
     // verilog_format: on
    `uvm_info(`gfn, $sformatf(
              "csr_write_mutex_claim: mutex claimed for interface %s", mutex_owner_write.name()),
              UVM_MEDIUM)
  endtask

  // Claim the mutex for the register reads
  virtual task csr_read_mutex_claim;
    lc_ctrl_csr_intf_e not_mutex_owner_read =
        (mutex_owner_read == LcCtrlTLUL) ? LcCtrlJTAG : LcCtrlTLUL;
    `uvm_info(`gfn, $sformatf(
              "csr_read_mutex_claim: claiming mutex for interface %s", mutex_owner_read.name()),
              UVM_MEDIUM)
    // verilog_format: off
    `DV_SPINWAIT(
        fork
          claim_mutex(mutex_owner_read);
          release_mutex(not_mutex_owner_read);
        join
        )
    // verilog_format: on
    `uvm_info(`gfn, $sformatf(
              "csr_read_mutex_claim: mutex claimed for interface %s", mutex_owner_read.name()),
              UVM_MEDIUM)
  endtask

  // Claim the Mutex for a particular interface
  virtual task claim_mutex(lc_ctrl_csr_intf_e sel);
    uvm_reg_data_t read_val = 0;

    while (read_val != CLAIM_TRANS_VAL) begin
      csr_wr(.ptr(m_claim_transition_if), .value(CLAIM_TRANS_VAL), .map(m_map[sel]));
      csr_rd(.ptr(m_claim_transition_if), .value(read_val), .map(m_map[sel]));
      `uvm_info(`gfn, $sformatf("claim_mutex: sel=%0d claim_transition_if = %8h", sel, read_val),
                UVM_MEDIUM)
    end
    // Read transition_regwen to make sure it is 1
    csr_rd(.ptr(m_transition_regwen), .value(read_val), .map(m_map[sel]));
    `DV_CHECK_EQ(read_val, 1)
  endtask

  // Release the Mutex for a particular interface
  virtual task release_mutex(lc_ctrl_csr_intf_e sel);
    uvm_reg_data_t read_val = CLAIM_TRANS_VAL;

    while (read_val == CLAIM_TRANS_VAL) begin
      csr_wr(.ptr(m_claim_transition_if), .value(0), .map(m_map[sel]));
      csr_rd(.ptr(m_claim_transition_if), .value(read_val), .map(m_map[sel]));
      `uvm_info(`gfn, $sformatf("release_mutex: sel=%0d claim_transition_if = %8h", sel, read_val),
                UVM_MEDIUM)
    end
    // Read transition_regwen to make sure it is 0
    csr_rd(.ptr(m_transition_regwen), .value(read_val), .map(m_map[sel]));
    `DV_CHECK_EQ(read_val, 0)

  endtask

  // Create a queue of register accesses
  virtual function void create_reg_accesses();
    m_reg_accesses.delete();
    foreach (m_mutex_regs[i]) begin
      m_reg_accesses.push_front('{r: m_mutex_regs[i], map_sel: LcCtrlTLUL,
                                blocking: $urandom_range(1, 0)});
      m_reg_accesses.push_front('{r: m_mutex_regs[i], map_sel: LcCtrlJTAG,
                                blocking: $urandom_range(1, 0)});
    end
  endfunction

endclass
