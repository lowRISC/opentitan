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
  int                     hart;
  riscv_privil_reg        mstatus;
  rand bit                mstatus_mie;
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
    string label = format_string({$sformatf("%0sinit_%0s:",
                                 hart_prefix(hart), mode.name())}, LABEL_STR_LEN);
    string ret_instr[] = {"mret"};
    riscv_privil_reg regs[$];
    label = label.tolower();
    setup_mmode_reg(mode, regs);
    if(mode == SUPERVISOR_MODE) begin
      setup_smode_reg(mode, regs);
    end
    if(mode == USER_MODE) begin
      setup_umode_reg(mode, regs);
    end
    if(cfg.virtual_addr_translation_on) begin
      setup_satp(instrs);
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
    if (cfg.randomize_csr) begin
      mstatus.set_val(cfg.mstatus);
    end
    mstatus.set_field("MPRV", cfg.mstatus_mprv);
    mstatus.set_field("MXR", cfg.mstatus_mxr);
    mstatus.set_field("SUM", cfg.mstatus_sum);
    mstatus.set_field("TVM", cfg.mstatus_tvm);
    mstatus.set_field("TW", cfg.set_mstatus_tw);
    mstatus.set_field("FS", cfg.mstatus_fs);
    mstatus.set_field("VS", cfg.mstatus_vs);
    if (!(SUPERVISOR_MODE inside {supported_privileged_mode}) && (XLEN != 32)) begin
      mstatus.set_field("SXL", 2'b00);
    end else if (XLEN == 64) begin
      mstatus.set_field("SXL", 2'b10);
    end
    if (!(USER_MODE inside {supported_privileged_mode}) && (XLEN != 32)) begin
      mstatus.set_field("UXL", 2'b00);
    end else if (XLEN == 64) begin
      mstatus.set_field("UXL", 2'b10);
    end
    mstatus.set_field("XS", 0);
    mstatus.set_field("SD", 0);
    mstatus.set_field("UIE", 0);
    // Set the previous privileged mode as the target mode
    mstatus.set_field("MPP", mode);
    mstatus.set_field("SPP", 0);
    // Enable interrupt
    // Only machine mode requires mstatus.MIE to be 1 for enabling interrupt
    if (mode == MACHINE_MODE) begin
      mstatus.set_field("MPIE", cfg.enable_interrupt);
    end else begin
      mstatus.set_field("MPIE", cfg.enable_interrupt & mstatus_mie);
    end
    // MIE is set when returning with mret, avoids trapping before returning
    mstatus.set_field("MIE", 0);
    mstatus.set_field("SPIE", cfg.enable_interrupt);
    mstatus.set_field("SIE",  cfg.enable_interrupt);
    mstatus.set_field("UPIE", cfg.enable_interrupt);
    mstatus.set_field("UIE", riscv_instr_pkg::support_umode_trap);
    `uvm_info(`gfn, $sformatf("mstatus_val: 0x%0x", mstatus.get_val()), UVM_LOW)
    regs.push_back(mstatus);
    // Enable external and timer interrupt
    if (MIE inside {implemented_csr}) begin
      mie = riscv_privil_reg::type_id::create("mie");
      mie.init_reg(MIE);
      if (cfg.randomize_csr) begin
        mie.set_val(cfg.mie);
      end
      mie.set_field("UEIE", cfg.enable_interrupt);
      mie.set_field("SEIE", cfg.enable_interrupt);
      mie.set_field("MEIE", cfg.enable_interrupt);
      mie.set_field("USIE", cfg.enable_interrupt);
      mie.set_field("SSIE", cfg.enable_interrupt);
      mie.set_field("MSIE", cfg.enable_interrupt);
      mie.set_field("MTIE", cfg.enable_interrupt & cfg.enable_timer_irq);
      mie.set_field("STIE", cfg.enable_interrupt & cfg.enable_timer_irq);
      mie.set_field("UTIE", cfg.enable_interrupt & cfg.enable_timer_irq);
      regs.push_back(mie);
    end
  endfunction

  virtual function void setup_smode_reg(privileged_mode_t mode, ref riscv_privil_reg regs[$]);
    sstatus = riscv_privil_reg::type_id::create("sstatus");
    sstatus.init_reg(SSTATUS);
    `DV_CHECK_RANDOMIZE_FATAL(sstatus, "cannot randomize sstatus")
    if (cfg.randomize_csr) begin
      sstatus.set_val(cfg.sstatus);
    end
    sstatus.set_field("SPIE", cfg.enable_interrupt);
    sstatus.set_field("SIE",  cfg.enable_interrupt);
    sstatus.set_field("UPIE", cfg.enable_interrupt);
    sstatus.set_field("UIE", riscv_instr_pkg::support_umode_trap);
    if(XLEN==64) begin
      sstatus.set_field("UXL", 2'b10);
    end
    sstatus.set_field("FS", cfg.mstatus_fs);
    sstatus.set_field("XS", 0);
    sstatus.set_field("SD", 0);
    sstatus.set_field("UIE", 0);
    sstatus.set_field("SPP", 0);
    regs.push_back(sstatus);
    // Enable external and timer interrupt
    if (SIE inside {implemented_csr}) begin
      sie = riscv_privil_reg::type_id::create("sie");
      sie.init_reg(SIE);
      if (cfg.randomize_csr) begin
        sie.set_val(cfg.sie);
      end
      sie.set_field("UEIE", cfg.enable_interrupt);
      sie.set_field("SEIE", cfg.enable_interrupt);
      sie.set_field("USIE", cfg.enable_interrupt);
      sie.set_field("SSIE", cfg.enable_interrupt);
      sie.set_field("STIE", cfg.enable_interrupt & cfg.enable_timer_irq);
      sie.set_field("UTIE", cfg.enable_interrupt & cfg.enable_timer_irq);
      regs.push_back(sie);
    end
  endfunction

  virtual function void setup_umode_reg(privileged_mode_t mode, ref riscv_privil_reg regs[$]);
    // For implementations that do not provide any U-mode CSRs, return immediately
    if (!riscv_instr_pkg::support_umode_trap) begin
      return;
    end
    ustatus = riscv_privil_reg::type_id::create("ustatus");
    ustatus.init_reg(USTATUS);
    `DV_CHECK_RANDOMIZE_FATAL(ustatus, "cannot randomize ustatus")
    if (cfg.randomize_csr) begin
      ustatus.set_val(cfg.ustatus);
    end
    ustatus.set_field("UIE", cfg.enable_interrupt);
    ustatus.set_field("UPIE", cfg.enable_interrupt);
    regs.push_back(ustatus);
    if (UIE inside {implemented_csr}) begin
      uie = riscv_privil_reg::type_id::create("uie");
      uie.init_reg(UIE);
      if (cfg.randomize_csr) begin
        uie.set_val(cfg.uie);
      end
      uie.set_field("UEIE", cfg.enable_interrupt);
      uie.set_field("USIE", cfg.enable_interrupt);
      uie.set_field("UTIE", cfg.enable_interrupt & cfg.enable_timer_irq);
      regs.push_back(uie);
    end
  endfunction

  virtual function void gen_csr_instr(riscv_privil_reg regs[$], ref string instrs[$]);
    foreach(regs[i]) begin
      instrs.push_back($sformatf("li x%0d, 0x%0x", cfg.gpr[0], regs[i].get_val()));
      instrs.push_back($sformatf("csrw 0x%0x, x%0d # %0s",
                       regs[i].reg_name, cfg.gpr[0], regs[i].reg_name.name()));
    end
  endfunction

  virtual function void setup_satp(ref string instrs[$]);
    riscv_privil_reg satp;
    bit [XLEN-1:0] satp_ppn_mask;
    if(SATP_MODE == BARE) return;
    satp = riscv_privil_reg::type_id::create("satp");
    satp.init_reg(SATP);
    satp.set_field("MODE", SATP_MODE);
    instrs.push_back($sformatf("li x%0d, 0x%0x", cfg.gpr[0], satp.get_val()));
    instrs.push_back($sformatf("csrw 0x%0x, x%0d # satp", SATP, cfg.gpr[0]));
    satp_ppn_mask = '1 >> (XLEN - satp.get_field_by_name("PPN").bit_width);
    // Load the root page table physical address
    instrs.push_back($sformatf("la x%0d, page_table_0", cfg.gpr[0]));
    // Right shift to get PPN at 4k granularity
    instrs.push_back($sformatf("srli x%0d, x%0d, 12", cfg.gpr[0], cfg.gpr[0]));
    instrs.push_back($sformatf("li   x%0d, 0x%0x", cfg.gpr[1], satp_ppn_mask));
    instrs.push_back($sformatf("and x%0d, x%0d, x%0d", cfg.gpr[0], cfg.gpr[0], cfg.gpr[1]));
    // Set the PPN field for SATP
    instrs.push_back($sformatf("csrs 0x%0x, x%0d # satp", SATP, cfg.gpr[0]));
  endfunction

endclass
