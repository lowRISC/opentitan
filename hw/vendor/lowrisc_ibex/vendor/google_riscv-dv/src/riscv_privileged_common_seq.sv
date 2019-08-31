/*
 * Copyright 2018 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// This class provides some common routines for privileged mode operations
class riscv_privileged_common_seq extends uvm_sequence;

  riscv_instr_gen_config  cfg;
  riscv_privil_reg        mstatus;
  riscv_privil_reg        mie;
  riscv_privil_reg        sstatus;
  riscv_privil_reg        sie;
  riscv_privil_reg        ustatus;
  riscv_privil_reg        uie;

  `uvm_object_utils(riscv_privileged_common_seq)

  function new(string name = "");
    super.new(name);
  endfunction

  virtual function void enter_privileged_mode(input privileged_mode_t mode,
                                              output string instrs[$]);
    string label = format_string({"init_", mode.name(), ":"}, LABEL_STR_LEN);
    string ret_instr[] = {"mret"};
    riscv_privil_reg regs[$];
    label = label.tolower();
    setup_mmode_reg(mode, regs);
    if(mode != MACHINE_MODE) begin
      setup_smode_reg(mode, regs);
      setup_satp(instrs);
      ret_instr.shuffle();
    end
    gen_csr_instr(regs, instrs);
    // Use mret/sret to switch to the target privileged mode
    instrs.push_back(ret_instr[0]);
    foreach(instrs[i]) begin
      instrs[i] = {indent, instrs[i]};
    end
    instrs.push_front(label);
  endfunction

  virtual function void setup_mmode_reg(privileged_mode_t mode, ref riscv_privil_reg regs[$]);
    mstatus = riscv_privil_reg::type_id::create("mstatus");
    mstatus.init_reg(MSTATUS);
    `DV_CHECK_RANDOMIZE_FATAL(mstatus, "cannot randomize mstatus");
    if(XLEN==64) begin
      mstatus.set_field("UXL", 2'b10);
      mstatus.set_field("SXL", 2'b10);
    end
    mstatus.set_field("XS", 0);
    mstatus.set_field("FS", 0);
    mstatus.set_field("SD", 0);
    mstatus.set_field("UIE", 0);
    mstatus.set_field("MPRV", cfg.mstatus_mprv);
    mstatus.set_field("MXR", cfg.mstatus_mxr);
    mstatus.set_field("SUM", cfg.mstatus_sum);
    mstatus.set_field("TVM", cfg.mstatus_tvm);
    // Set the previous privileged mode as the target mode
    mstatus.set_field("MPP", mode);
    if(mode == USER_MODE)
      mstatus.set_field("SPP", 0);
    else
      mstatus.set_field("SPP", 1);
    // Enable interrupt
    mstatus.set_field("MPIE", cfg.enable_interrupt);
    mstatus.set_field("MIE", cfg.enable_interrupt);
    mstatus.set_field("SPIE", cfg.enable_interrupt);
    mstatus.set_field("SIE",  cfg.enable_interrupt);
    mstatus.set_field("UPIE", cfg.enable_interrupt);
    mstatus.set_field("UIE", riscv_instr_pkg::support_umode_trap);
    regs.push_back(mstatus);
    // Enable external and timer interrupt
    if (MIE inside {implemented_csr}) begin
      mie = riscv_privil_reg::type_id::create("mie");
      mie.init_reg(MIE);
      mie.set_field("UEIE", cfg.enable_interrupt);
      mie.set_field("SEIE", cfg.enable_interrupt);
      mie.set_field("MEIE", cfg.enable_interrupt);
      mie.set_field("USIE", cfg.enable_interrupt);
      mie.set_field("SSIE", cfg.enable_interrupt);
      mie.set_field("MSIE", cfg.enable_interrupt);
      regs.push_back(mie);
    end
  endfunction

  virtual function void setup_smode_reg(privileged_mode_t mode, ref riscv_privil_reg regs[$]);
    sstatus = riscv_privil_reg::type_id::create("sstatus");
    sstatus.init_reg(SSTATUS);
    `DV_CHECK_RANDOMIZE_FATAL(sstatus, "cannot randomize sstatus")
    sstatus.set_field("SPIE", cfg.enable_interrupt);
    sstatus.set_field("SIE",  cfg.enable_interrupt);
    sstatus.set_field("UPIE", cfg.enable_interrupt);
    sstatus.set_field("UIE", riscv_instr_pkg::support_umode_trap);
    if(XLEN==64) begin
      sstatus.set_field("UXL", 2'b10);
    end
    sstatus.set_field("XS", 0);
    sstatus.set_field("FS", 0);
    sstatus.set_field("SD", 0);
    sstatus.set_field("UIE", 0);
    if(mode == USER_MODE)
      sstatus.set_field("SPP", 0);
    else
      sstatus.set_field("SPP", 1);
    regs.push_back(sstatus);
    // Enable external and timer interrupt
    if (SIE inside {implemented_csr}) begin
      sie = riscv_privil_reg::type_id::create("sie");
      sie.init_reg(SIE);
      sie.set_field("UEIE", cfg.enable_interrupt);
      sie.set_field("SEIE", cfg.enable_interrupt);
      sie.set_field("USIE", cfg.enable_interrupt);
      sie.set_field("SSIE", cfg.enable_interrupt);
      regs.push_back(sie);
    end
  endfunction

  virtual function void setup_umode_reg(privileged_mode_t mode, ref riscv_privil_reg regs[$]);
    ustatus = riscv_privil_reg::type_id::create("ustatus");
    ustatus.init_reg(USTATUS);
    `DV_CHECK_RANDOMIZE_FATAL(ustatus, "cannot randomize ustatus")
    ustatus.set_field("UIE", cfg.enable_interrupt);
    ustatus.set_field("UPIE", cfg.enable_interrupt);
    regs.push_back(ustatus);
    if (UIE inside {implemented_csr}) begin
      uie = riscv_privil_reg::type_id::create("uie");
      uie.init_reg(UIE);
      uie.set_field("UEIE", cfg.enable_interrupt);
      uie.set_field("USIE", cfg.enable_interrupt);
      regs.push_back(uie);
    end
  endfunction

  virtual function void gen_csr_instr(riscv_privil_reg regs[$], ref string instrs[$]);
    foreach(regs[i]) begin
      instrs.push_back($sformatf("li a0, 0x%0x", regs[i].get_val()));
      instrs.push_back($sformatf("csrw 0x%0x, a0 # %0s",
                       regs[i].reg_name, regs[i].reg_name.name()));
    end
  endfunction

  virtual function void setup_satp(ref string instrs[$]);
    riscv_privil_reg satp;
    bit [XLEN-1:0] satp_ppn_mask;
    if(SATP_MODE == BARE) return;
    satp = riscv_privil_reg::type_id::create("satp");
    satp.init_reg(SATP);
    satp.set_field("MODE", SATP_MODE);
    instrs.push_back($sformatf("li a0, 0x%0x", satp.get_val()));
    instrs.push_back($sformatf("csrw 0x%0x, a0 // satp", SATP));
    satp_ppn_mask = '1 >> (XLEN - satp.get_field_by_name("PPN").bit_width);
    // Load the root page table physical address
    instrs.push_back("la a0, page_table_0");
    // Right shift to get PPN at 4k granularity
    instrs.push_back("srli a0, a0, 12");
    instrs.push_back($sformatf("li   a1, 0x%0x", satp_ppn_mask));
    instrs.push_back("and a0, a0, a1");
    // Set the PPN field for SATP
    instrs.push_back($sformatf("csrs 0x%0x, a0 // satp", SATP));
  endfunction

endclass
