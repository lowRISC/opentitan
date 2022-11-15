// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "spike_cosim.h"
#include "riscv/config.h"
#include "riscv/decode.h"
#include "riscv/devices.h"
#include "riscv/log_file.h"
#include "riscv/processor.h"
#include "riscv/simif.h"

#include <cassert>
#include <iostream>
#include <sstream>

// For a short time, we're going to support building against version
// ibex-cosim-v0.2 (20a886c) and also ibex-cosim-v0.3 (9af9730). Unfortunately,
// they've got different APIs and spike doesn't expose a version string.
//
// However, a bit of digging around finds some defines that have been added
// between the two versions.
//
// TODO: Once there's been a bit of a window to avoid a complete flag day,
//       remove this ugly hack!
#ifndef HGATP_MODE_SV57X4
#define OLD_SPIKE
#endif

#ifndef OLD_SPIKE
#include "riscv/isa_parser.h"
#endif

SpikeCosim::SpikeCosim(const std::string &isa_string, uint32_t start_pc,
                       uint32_t start_mtvec, const std::string &trace_log_path,
                       bool secure_ibex, bool icache_en,
                       uint32_t pmp_num_regions, uint32_t pmp_granularity,
                       uint32_t mhpm_counter_num)
    : nmi_mode(false), pending_iside_error(false), insn_cnt(0) {
  FILE *log_file = nullptr;
  if (trace_log_path.length() != 0) {
    log = std::make_unique<log_file_t>(trace_log_path.c_str());
    log_file = log->get();
  }

#ifdef OLD_SPIKE
  processor =
      std::make_unique<processor_t>(isa_string.c_str(), "MU", DEFAULT_VARCH,
                                    this, 0, false, log_file, std::cerr);
#else
  isa_parser = std::make_unique<isa_parser_t>(isa_string.c_str(), "MU");

  processor = std::make_unique<processor_t>(
      isa_parser.get(), DEFAULT_VARCH, this, 0, false, log_file, std::cerr);
#endif

  processor->set_pmp_num(pmp_num_regions);
  processor->set_mhpm_counter_num(mhpm_counter_num);
  processor->set_pmp_granularity(1 << (pmp_granularity + 2));
  processor->set_ibex_flags(secure_ibex, icache_en);

  initial_proc_setup(start_pc, start_mtvec, mhpm_counter_num);

  if (log) {
    processor->set_debug(true);
    processor->enable_log_commits();
  }
}

// always return nullptr so all memory accesses go via mmio_load/mmio_store
char *SpikeCosim::addr_to_mem(reg_t addr) { return nullptr; }

bool SpikeCosim::mmio_load(reg_t addr, size_t len, uint8_t *bytes) {
  bool bus_error = !bus.load(addr, len, bytes);

  bool dut_error = false;

  // Incoming access may be an iside or dside access. Use PC to help determine
  // which.
  uint32_t pc = processor->get_state()->pc;
  uint32_t aligned_addr = addr & 0xfffffffc;

  if (pending_iside_error && (aligned_addr == pending_iside_err_addr)) {
    // Check if the incoming access is subject to an iside error, in which case
    // assume it's an iside access and produce an error.
    pending_iside_error = false;
    dut_error = true;
  } else if (addr < pc || addr >= (pc + 8)) {
    // Spike may attempt to access up to 8-bytes from the PC when fetching, so
    // only check as a dside access when it falls outside that range.

    // Otherwise check if the aligned PC matches with the aligned address or an
    // incremented aligned PC (to capture the unaligned 4-byte instruction
    // case). Assume a successful iside access if either of these checks are
    // true, otherwise assume a dside access and check against DUT dside
    // accesses.  If the RTL produced a bus error for the access, or the
    // checking failed produce a memory fault in spike.
    dut_error = (check_mem_access(false, addr, len, bytes) != kCheckMemOk);
  }

  return !(bus_error || dut_error);
}

bool SpikeCosim::mmio_store(reg_t addr, size_t len, const uint8_t *bytes) {
  bool bus_error = !bus.store(addr, len, bytes);
  // If the RTL produced a bus error for the access, or the checking failed
  // produce a memory fault in spike.
  bool dut_error = (check_mem_access(true, addr, len, bytes) != kCheckMemOk);

  return !(bus_error || dut_error);
}

void SpikeCosim::proc_reset(unsigned id) {}

const char *SpikeCosim::get_symbol(uint64_t addr) { return nullptr; }

void SpikeCosim::add_memory(uint32_t base_addr, size_t size) {
  auto new_mem = std::make_unique<mem_t>(size);
  bus.add_device(base_addr, new_mem.get());
  mems.emplace_back(std::move(new_mem));
}

bool SpikeCosim::backdoor_write_mem(uint32_t addr, size_t len,
                                    const uint8_t *data_in) {
  return bus.store(addr, len, data_in);
}

bool SpikeCosim::backdoor_read_mem(uint32_t addr, size_t len,
                                   uint8_t *data_out) {
  return bus.load(addr, len, data_out);
}

// When we call processor->step(), spike advances to the next pc IFF a trap does
// not occur. If a trap does occur, state.last_inst_pc is set to PC_INVALID, and
// we need to call step() again to actually execute the first instruction of the
// trap handler.
// This sentinel value PC_INVALID of state.last_inst_pc allows the cosimulation
// testbench to detect when spike is in this transient state, where we have
// attempted to step but have taken a trap instead and not actually executed
// another instruction.
//
// The flow of spike goes something like this...
// - Start of processor_t::step()
//   Set state.last_inst_pc to PC_INVALID. This is only set back to a
//   non-sentinel valid pc if the processor is able to completely execute the
//   next instruction. It is set back to a valid pc at the end of
//   execute_insn().
// - When calling execute_insn(), we try/except the fetch.func(), which
//   eventually calls one of the templated instructions in insn_template.cc.
//   These functions return the npc. From fetch.func(), we expect to catch
//   the exceptions (wait_for_interrupt_t, mem_trap_t&), which don't finish
//   executing the insn, but do result in printing to the log and re-throwing
//   the exception to be caught up one level by the step() function.
// - In step(), while trying to execute an instruction (down either the
//   fast/slow paths), we can catch an exception (trap_t&, triggers::matched_t&,
//   wait_for_interrupt_t), which means the pc never gets advanced. The pc only
//   gets advanced right at the end of the main paths if nothing goes awry (In
//   the macro advance_pc()).
//   The state.last_inst_pc also remains with the sentinel value PC_INVALID.
// - If we catch a trap_t&, then the take_trap() fn updates the state of the
//   processor, and when we call step() again we start executing in the new
//   context of the trap (trap andler, new MSTATUS, debug rom, etc. etc.)
bool SpikeCosim::step(uint32_t write_reg, uint32_t write_reg_data, uint32_t pc,
                      bool sync_trap, bool suppress_reg_write) {
  assert(write_reg < 32);

  // The DUT has just produced an RVFI item
  // (parameters of this func is the data in the RVFI item).

  // First check to see if this is an ebreak that should enter debug mode. These
  // need specific handling. When spike steps over them it'll immediately step
  // the next instruction (i.e. the first instruction of the debug handler) too.
  // In effect it treats it as a transition to debug mode that doesn't retire
  // any instruction so needs to execute the next instruction to step a single
  // time. To deal with this if it's a debug ebreak we skip the rest of this
  // function checking a few invariants on the debug ebreak first.
  if (pc_is_debug_ebreak(pc)) {
    return check_debug_ebreak(write_reg, pc, sync_trap);
  }

  uint32_t initial_spike_pc;
  uint32_t suppressed_write_reg;
  uint32_t suppressed_write_reg_data;
  bool pending_sync_exception = false;

  if (suppress_reg_write) {
    // If Ibex suppressed a register write (which occurs when a load gets data
    // with bad integrity) record the state of the destination register before
    // we do the stop, so we can restore it after the step (as spike won't
    // suppressed the register write).
    //
    // First check retired instruciton to ensure load suppression is correct
    if (!check_suppress_reg_write(write_reg, pc, suppressed_write_reg)) {
      return false;
    }

    // The check gives us the destination register the instruction would have
    // written to (write_reg will be 0 to indicate to write). Record the
    // contents of that register.
    suppressed_write_reg_data =
        processor->get_state()->XPR[suppressed_write_reg];
  }

  // Before stepping Spike, record the current spike pc.
  // (If the current step causes a synchronous trap, it will be
  //  recorded against the current pc)
  initial_spike_pc = (processor->get_state()->pc & 0xffffffff);
  processor->step(1);

  // ISS
  // - If encountered an async trap,
  //    - PC_INVALID == true
  //    - step again to execute 1st instr of handler
  // - If encountered a sync trap,
  //    - PC_INVALID == true
  //    - current state is that of the trapping instruction
  //    - step again to execute 1st instr of handler
  // - If encountering a sync trap, immediately upon trying to jump to a async
  //      trap handler, (the reverse is not possible, as async traps are
  //      disabled upon entering a handler)
  //    - PC_INVALID == true
  //    - current state is that of the trapping instruction
  // DUT
  // - If the dut encounters an async trap (which can be thought of as occuring
  //   between instructions), an rvfi_item will be generated for the the first
  //   retired instruction of the trap handler.
  // - If the dut encounters a sync trap, an rvfi_item will be generated for the
  //   trapping instruction, with sync_trap == True. (The trapping instruction
  //   is presented on the RVFI but was not retired.)

  if (processor->get_state()->last_inst_pc == PC_INVALID) {
    if (!(processor->get_state()->mcause->read() & 0x80000000) ||
        processor->get_state()
            ->debug_mode) {  // (Async-Traps are disabled in debug mode)
      // Spike encountered a synchronous trap
      pending_sync_exception = true;

    } else {
      // Spike encountered an asynchronous trap.

      // Step to the first instruction of the ISR.
      initial_spike_pc = (processor->get_state()->pc & 0xffffffff);
      processor->step(1);

      if (processor->get_state()->last_inst_pc == PC_INVALID) {
        // If we see PC_INVALID here, the first instr of the ISR must cause an
        // exception, as interrupts are now disabled.
        pending_sync_exception = true;
      }
    }

    // If spike has advanced to be at a synchronous trap, now check that it
    // matches the reported dut behaviour.
    if (pending_sync_exception) {
      if (!sync_trap) {
        std::stringstream err_str;
        err_str << "Synchronous trap was expected at ISS PC: "
                << std::hex << processor->get_state()->pc
                << " but the DUT didn't report one at PC " << pc;
        errors.emplace_back(err_str.str());
        return false;
      }

      if (!check_sync_trap(write_reg, pc, initial_spike_pc)) {
        return false;
      }

      handle_cpuctrl_exception_entry();

      // This is all the checking possible when consider a
      // synchronously-trapping instruction that never retired.
      return true;
    }
  }

  // We reached a retired instruction, so check spike and the dut behaved
  // consistently.

  if (!sync_trap && pc_is_mret(pc)) {
    change_cpuctrlsts_sync_exc_seen(false);

    if (nmi_mode) {
      // Do handling for recoverable NMI
      leave_nmi_mode();
    }
  }

  if (pending_iside_error) {
    std::stringstream err_str;
    err_str << "DUT generated an iside error for address: "
            << std::hex << pending_iside_err_addr
            << " but the ISS didn't produce one";
    errors.emplace_back(err_str.str());
    return false;
  }
  pending_iside_error = false;

  if (suppress_reg_write) {
    // If we suppressed a register write restore the old register state now
    processor->get_state()->XPR.write(suppressed_write_reg,
                                      suppressed_write_reg_data);
  }

  if (!check_retired_instr(write_reg, write_reg_data, pc, suppress_reg_write)) {
    return false;
  }

  // Only increment insn_cnt and return true if there are no errors
  insn_cnt++;
  return true;
}

bool SpikeCosim::check_retired_instr(uint32_t write_reg,
                                     uint32_t write_reg_data, uint32_t dut_pc,
                                     bool suppress_reg_write) {
  // Check the retired instruction and all of its side-effects match those from
  // the DUT

  // Check PC of executed instruction matches the expected PC
  // TODO: Confirm details of why spike sign extends PC, something to do with
  // 32-bit address as 64-bit address must be sign extended?
  if ((processor->get_state()->last_inst_pc & 0xffffffff) != dut_pc) {
    std::stringstream err_str;
    err_str << "PC mismatch, DUT retired : " << std::hex << dut_pc
            << " , but the ISS retired: "
            << std::hex << processor->get_state()->last_inst_pc;
    errors.emplace_back(err_str.str());
    return false;
  }

  // Check register writes from executed instruction match what is expected
  auto &reg_changes = processor->get_state()->log_reg_write;

  bool gpr_write_seen = false;

  for (auto reg_change : reg_changes) {
    // reg_change.first provides register type in bottom 4 bits, then register
    // index above that

    // Ignore writes to x0
    if (reg_change.first == 0)
      continue;

    if ((reg_change.first & 0xf) == 0) {
      // register is GPR
      // should never see more than one GPR write per step
      assert(!gpr_write_seen);

      if (!suppress_reg_write &&
          !check_gpr_write(reg_change, write_reg, write_reg_data)) {
        return false;
      }

      gpr_write_seen = true;
    } else if ((reg_change.first & 0xf) == 4) {
      // register is CSR
      on_csr_write(reg_change);
    } else {
      // should never see other types
      assert(false);
    }
  }

  if (write_reg != 0 && !gpr_write_seen) {
    std::stringstream err_str;
    err_str << "DUT wrote register x" << write_reg
            << " but a write was not expected" << std::endl;
    errors.emplace_back(err_str.str());
    return false;
  }

  // Errors may have been generated outside of step()
  // (e.g. in check_mem_access()).
  if (errors.size() != 0) {
    return false;
  }

  return true;
}

bool SpikeCosim::check_sync_trap(uint32_t write_reg,
                                 uint32_t dut_pc, uint32_t initial_spike_pc) {
  // Check if an synchronously-trapping instruction matches
  // between Spike and the DUT.

  // Check that both spike and DUT trapped on the same pc
  if (initial_spike_pc != dut_pc) {
    std::stringstream err_str;
    err_str << "PC mismatch at synchronous trap, DUT at pc: "
            << std::hex << dut_pc
            << "while ISS pc is at : "
            << std::hex << initial_spike_pc;
    errors.emplace_back(err_str.str());
    return false;
  }

  // A sync trap should not have any side-effects, as the instruction appears on
  // the DUT RVFI but is not actually retired.
  if (write_reg != 0) {
    std::stringstream err_str;
    err_str << "Synchronous trap occurred at PC: " << std::hex << dut_pc
            << "but DUT wrote to register: x" << std::dec << write_reg;
    errors.emplace_back(err_str.str());
    return false;
  }

  // If we see an internal NMI, that means we receive an extra memory intf item.
  // Deleting that is necessary since next Load/Store would fail otherwise.
  if (processor->get_state()->mcause->read() == 0xFFFFFFE0) {
    pending_dside_accesses.erase(pending_dside_accesses.begin());
  }

  // Errors may have been generated outside of step() (e.g. in
  // check_mem_access()), return false if there are any.
  if (errors.size() != 0) {
    return false;
  }

  return true;
}

bool SpikeCosim::check_gpr_write(const commit_log_reg_t::value_type &reg_change,
                                 uint32_t write_reg, uint32_t write_reg_data) {
  uint32_t cosim_write_reg = (reg_change.first >> 4) & 0x1f;

  if (write_reg == 0) {
    std::stringstream err_str;
    err_str << "DUT didn't write to register x" << cosim_write_reg
            << ", but a write was expected";
    errors.emplace_back(err_str.str());

    return false;
  }

  if (write_reg != cosim_write_reg) {
    std::stringstream err_str;
    err_str << "Register write index mismatch, DUT: x" << write_reg
            << " expected: x" << cosim_write_reg;
    errors.emplace_back(err_str.str());

    return false;
  }

  // TODO: Investigate why this fails (may be because spike can produce PCs
  // with high 32 bits set).
  // assert((reg_change.second.v[0] & 0xffffffff00000000) == 0);
  uint32_t cosim_write_reg_data = reg_change.second.v[0];

  if (write_reg_data != cosim_write_reg_data) {
    std::stringstream err_str;
    err_str << "Register write data mismatch to x" << cosim_write_reg
            << " DUT: " << std::hex << write_reg_data
            << " expected: " << cosim_write_reg_data;
    errors.emplace_back(err_str.str());

    return false;
  }

  return true;
}

bool SpikeCosim::check_suppress_reg_write(uint32_t write_reg, uint32_t pc,
                                          uint32_t &suppressed_write_reg) {
  if (write_reg != 0) {
    std::stringstream err_str;
    err_str << "Instruction at " << std::hex << pc
            << " indicated a suppressed register write but wrote to x"
            << std::dec << write_reg;
    errors.emplace_back(err_str.str());

    return false;
  }

  if (!pc_is_load(pc, suppressed_write_reg)) {
    std::stringstream err_str;
    err_str << "Instruction at " << std::hex << pc
            << " indicated a suppressed register write is it not a load"
               " only loads can suppress register writes";
    errors.emplace_back(err_str.str());

    return false;
  }

  return true;
}

void SpikeCosim::on_csr_write(const commit_log_reg_t::value_type &reg_change) {
  int cosim_write_csr = (reg_change.first >> 4) & 0xfff;

  // TODO: Investigate why this fails (may be because spike can produce PCs
  // with high 32 bits set).
  // assert((reg_change.second.v[0] & 0xffffffff00000000) == 0);
  uint32_t cosim_write_csr_data = reg_change.second.v[0];

  // Spike and Ibex have different WARL behaviours so after any CSR write
  // check the fields and adjust to match Ibex behaviour.
  fixup_csr(cosim_write_csr, cosim_write_csr_data);
}

void SpikeCosim::leave_nmi_mode() {
  nmi_mode = false;

  // Restore CSR status from mstack
  uint32_t mstatus = processor->get_csr(CSR_MSTATUS);
  mstatus = set_field(mstatus, MSTATUS_MPP, mstack.mpp);
  mstatus = set_field(mstatus, MSTATUS_MPIE, mstack.mpie);
#ifdef OLD_SPIKE
  processor->set_csr(CSR_MSTATUS, mstatus);

  processor->set_csr(CSR_MEPC, mstack.epc);
  processor->set_csr(CSR_MCAUSE, mstack.cause);
#else
  processor->put_csr(CSR_MSTATUS, mstatus);

  processor->put_csr(CSR_MEPC, mstack.epc);
  processor->put_csr(CSR_MCAUSE, mstack.cause);
#endif
}

void SpikeCosim::handle_cpuctrl_exception_entry() {
  if (!processor->get_state()->debug_mode) {
    bool old_sync_exc_seen = change_cpuctrlsts_sync_exc_seen(true);
    if (old_sync_exc_seen) {
      set_cpuctrlsts_double_fault_seen();
    }
  }
}

bool SpikeCosim::change_cpuctrlsts_sync_exc_seen(bool flag) {
  bool old_flag = false;
  uint32_t cpuctrlsts = processor->get_csr(CSR_CPUCTRLSTS);

  // If sync_exc_seen (bit 6) is already set update old_flag to match
  if (cpuctrlsts & 0x40) {
    old_flag = true;
  }

  cpuctrlsts = (cpuctrlsts & 0x1bf) | (flag ? 0x40 : 0);
  processor->put_csr(CSR_CPUCTRLSTS, cpuctrlsts);

  return old_flag;
}

void SpikeCosim::set_cpuctrlsts_double_fault_seen() {
  uint32_t cpuctrlsts = processor->get_csr(CSR_CPUCTRLSTS);
  // Set double_fault_seen  (bit 7)
  cpuctrlsts = (cpuctrlsts & 0x17f) | 0x80;
  processor->put_csr(CSR_CPUCTRLSTS, cpuctrlsts);
}

void SpikeCosim::initial_proc_setup(uint32_t start_pc, uint32_t start_mtvec,
                                    uint32_t mhpm_counter_num) {
  processor->get_state()->pc = start_pc;
  processor->get_state()->mtvec->write(start_mtvec);

  processor->get_state()->csrmap[CSR_MARCHID] =
      std::make_shared<const_csr_t>(processor.get(), CSR_MARCHID, IBEX_MARCHID);

  processor->set_mmu_capability(IMPL_MMU_SBARE);

  for (int i = 0; i < processor->TM.count(); ++i) {
    processor->TM.tdata2_write(processor.get(), i, 0);
    processor->TM.tdata1_write(processor.get(), i, 0x28001048);
  }

  for (int i = 0; i < mhpm_counter_num; i++) {
    processor->get_state()->csrmap[CSR_MHPMEVENT3 + i] =
        std::make_shared<const_csr_t>(processor.get(), CSR_MHPMEVENT3 + i,
                                      1 << i);
  }
}

void SpikeCosim::set_mip(uint32_t mip) {
  processor->get_state()->mip->write_with_mask(0xffffffff, mip);
}

void SpikeCosim::set_nmi(bool nmi) {
  if (nmi && !nmi_mode && !processor->get_state()->debug_mode) {
    processor->get_state()->nmi = true;
    nmi_mode = true;

    // When NMI is set it is guaranteed NMI trap will be taken at the next step
    // so save CSR state for recoverable NMI to mstack now.
    mstack.mpp = get_field(processor->get_csr(CSR_MSTATUS), MSTATUS_MPP);
    mstack.mpie = get_field(processor->get_csr(CSR_MSTATUS), MSTATUS_MPIE);
    mstack.epc = processor->get_csr(CSR_MEPC);
    mstack.cause = processor->get_csr(CSR_MCAUSE);
  }
}

void SpikeCosim::set_nmi_int(bool nmi_int) {
  if (nmi_int && !nmi_mode && !processor->get_state()->debug_mode) {
    processor->get_state()->nmi_int = true;
    nmi_mode = true;

    // When NMI is set it is guaranteed NMI trap will be taken at the next step
    // so save CSR state for recoverable NMI to mstack now.
    mstack.mpp = get_field(processor->get_csr(CSR_MSTATUS), MSTATUS_MPP);
    mstack.mpie = get_field(processor->get_csr(CSR_MSTATUS), MSTATUS_MPIE);
    mstack.epc = processor->get_csr(CSR_MEPC);
    mstack.cause = processor->get_csr(CSR_MCAUSE);
  }
}

void SpikeCosim::set_debug_req(bool debug_req) {
  processor->halt_request =
      debug_req ? processor_t::HR_REGULAR : processor_t::HR_NONE;
}

void SpikeCosim::set_mcycle(uint64_t mcycle) {
  uint32_t upper_mcycle = mcycle >> 32;
  uint32_t lower_mcycle = mcycle & 0xffffffff;

  // Spike decrements the MCYCLE CSR when you write to it to hack around an
  // issue it has with incorrectly setting minstret/mcycle when there's an
  // explicit write to them. There's no backdoor write available via the public
  // interface to skip this. To complicate matters we can only write 32 bits at
  // a time and get a decrement each time.

  // Write the lower half first, incremented twice due to the double decrement
  processor->get_state()->csrmap[CSR_MCYCLE]->write(lower_mcycle + 2);

  if ((processor->get_state()->csrmap[CSR_MCYCLE]->read() & 0xffffffff) == 0) {
    // If the lower half is 0 at this point then the upper half will get
    // decremented, so increment it first.
    upper_mcycle++;
  }

  // Set the upper half
  processor->get_state()->csrmap[CSR_MCYCLEH]->write(upper_mcycle);

  // TODO: Do a neater job of this, a more recent spike release should allow us
  // to write all 64 bits at once at least.
}

void SpikeCosim::set_csr(const int csr_num, const uint32_t new_val) {
  // Note that this is tested with ibex-cosim-v0.3 version of Spike. 'set_csr'
  // method might have a hardwired zero for mhpmcounterX registers.
#ifdef OLD_SPIKE
  processor->set_csr(csr_num, new_val);
#else
  processor->put_csr(csr_num, new_val);
#endif
}

void SpikeCosim::set_ic_scr_key_valid(bool valid) {
  processor->set_ic_scr_key_valid(valid);
}

void SpikeCosim::notify_dside_access(const DSideAccessInfo &access_info) {
  // Address must be 32-bit aligned
  assert((access_info.addr & 0x3) == 0);

  pending_dside_accesses.emplace_back(
      PendingMemAccess{.dut_access_info = access_info, .be_spike = 0});
}

void SpikeCosim::set_iside_error(uint32_t addr) {
  // Address must be 32-bit aligned
  assert((addr & 0x3) == 0);

  pending_iside_error = true;
  pending_iside_err_addr = addr;
}

const std::vector<std::string> &SpikeCosim::get_errors() { return errors; }

void SpikeCosim::clear_errors() { errors.clear(); }

void SpikeCosim::fixup_csr(int csr_num, uint32_t csr_val) {
  switch (csr_num) {
    case CSR_MSTATUS: {
      reg_t mask =
          MSTATUS_MIE | MSTATUS_MPIE | MSTATUS_MPRV | MSTATUS_MPP | MSTATUS_TW;

      reg_t new_val = csr_val & mask;
#ifdef OLD_SPIKE
      processor->set_csr(csr_num, new_val);
#else
      processor->put_csr(csr_num, new_val);
#endif
      break;
    }
    case CSR_MCAUSE: {
      uint32_t any_interrupt = csr_val & 0x80000000;
      uint32_t int_interrupt = csr_val & 0x40000000;

      reg_t new_val = (csr_val & 0x0000001f) | any_interrupt;

      if (any_interrupt && int_interrupt) {
        new_val |= 0x7fffffe0;
      }

#ifdef OLD_SPIKE
      processor->set_csr(csr_num, new_val);
#else
      processor->put_csr(csr_num, new_val);
#endif
      break;
    }
  }
}

SpikeCosim::check_mem_result_e SpikeCosim::check_mem_access(
    bool store, uint32_t addr, size_t len, const uint8_t *bytes) {
  assert(len >= 1 && len <= 4);
  // Expect that no spike memory accesses cross a 32-bit boundary
  assert(((addr + (len - 1)) & 0xfffffffc) == (addr & 0xfffffffc));

  std::string iss_action = store ? "store" : "load";

  // Check if there are any pending DUT accesses to check against
  if (pending_dside_accesses.size() == 0) {
    std::stringstream err_str;
    err_str << "A " << iss_action << " at address " << std::hex << addr
            << " was expected but there are no pending accesses";
    errors.emplace_back(err_str.str());

    return kCheckMemCheckFailed;
  }

  auto &top_pending_access = pending_dside_accesses.front();
  auto &top_pending_access_info = top_pending_access.dut_access_info;

  std::string dut_action = top_pending_access_info.store ? "store" : "load";

  // Check for an address match
  uint32_t aligned_addr = addr & 0xfffffffc;
  if (aligned_addr != top_pending_access_info.addr) {
    std::stringstream err_str;
    err_str << "DUT generated " << dut_action << " at address " << std::hex
            << top_pending_access_info.addr << " but " << iss_action
            << " at address " << aligned_addr << " was expected";
    errors.emplace_back(err_str.str());

    return kCheckMemCheckFailed;
  }

  // Check access type match
  if (store != top_pending_access_info.store) {
    std::stringstream err_str;
    err_str << "DUT generated " << dut_action << " at addr " << std::hex
            << top_pending_access_info.addr << " but a " << iss_action
            << " was expected";
    errors.emplace_back(err_str.str());

    return kCheckMemCheckFailed;
  }

  // Calculate bytes within aligned 32-bit word that spike has accessed
  uint32_t expected_be = ((1 << len) - 1) << (addr & 0x3);

  bool pending_access_done = false;
  bool misaligned = top_pending_access_info.misaligned_first ||
                    top_pending_access_info.misaligned_second;

  if (misaligned) {
    // For misaligned accesses spike will generated multiple single byte
    // accesses where the DUT will generate an access covering all bytes within
    // an aligned 32-bit word.

    // Check bytes accessed this time haven't already been been seen for the DUT
    // access we are trying to match against
    if ((expected_be & top_pending_access.be_spike) != 0) {
      std::stringstream err_str;
      err_str << "DUT generated " << dut_action << " at address " << std::hex
              << top_pending_access_info.addr << " with BE "
              << top_pending_access_info.be << " and expected BE "
              << expected_be << " has been seen twice, so far seen "
              << top_pending_access.be_spike;

      errors.emplace_back(err_str.str());

      return kCheckMemCheckFailed;
    }

    // Check expected access isn't trying to access bytes that the DUT access
    // didn't access.
    if ((expected_be & ~top_pending_access_info.be) != 0) {
      std::stringstream err_str;
      err_str << "DUT generated " << dut_action << " at address " << std::hex
              << top_pending_access_info.addr << " with BE "
              << top_pending_access_info.be << " but expected BE "
              << expected_be << " has other bytes enabled";
      errors.emplace_back(err_str.str());
      return kCheckMemCheckFailed;
    }

    // Record which bytes have been seen from spike
    top_pending_access.be_spike |= expected_be;

    // If all bytes have been seen from spike we're done with this DUT access
    if (top_pending_access.be_spike == top_pending_access_info.be) {
      pending_access_done = true;
    }
  } else {
    // For aligned accesses bytes from spike access must precisely match bytes
    // from DUT access in one go
    if (expected_be != top_pending_access_info.be) {
      std::stringstream err_str;
      err_str << "DUT generated " << dut_action << " at address " << std::hex
              << top_pending_access_info.addr << " with BE "
              << top_pending_access_info.be << " but BE " << expected_be
              << " was expected";
      errors.emplace_back(err_str.str());

      return kCheckMemCheckFailed;
    }

    pending_access_done = true;
  }

  // Check data from expected access matches pending DUT access.
  // Data is ignored on error responses to loads so don't check it. Always check
  // store data.
  if (store || !top_pending_access_info.error) {
    // Combine bytes into a single word
    uint32_t expected_data = 0;
    for (int i = 0; i < len; ++i) {
      expected_data |= bytes[i] << (i * 8);
    }

    // Shift bytes into their position within an aligned 32-bit word
    expected_data <<= (addr & 0x3) * 8;

    // Mask off bytes expected access doesn't touch and check bytes match for
    // those that it does
    uint32_t expected_be_bits = (((uint64_t)1 << (len * 8)) - 1)
                                << ((addr & 0x3) * 8);
    uint32_t masked_dut_data = top_pending_access_info.data & expected_be_bits;

    if (expected_data != masked_dut_data) {
      std::stringstream err_str;
      err_str << "DUT generated " << iss_action << " at address " << std::hex
              << top_pending_access_info.addr << " with data "
              << masked_dut_data << " but data " << expected_data
              << " was expected with byte mask " << expected_be;

      errors.emplace_back(err_str.str());

      return kCheckMemCheckFailed;
    }
  }

  bool pending_access_error = top_pending_access_info.error;

  if (pending_access_error && misaligned) {
    // When misaligned accesses see an error, if they have crossed a 32-bit
    // boundary DUT will generate two accesses. If the top pending access from
    // the DUT was the first half of a misaligned access which accesses the top
    // byte, it must have crossed the 32-bit boundary and generated a second
    // access
    if (top_pending_access_info.misaligned_first &&
        ((top_pending_access_info.be & 0x8) != 0)) {
      // Check the second access DUT exists
      if ((pending_dside_accesses.size() < 2) ||
          !pending_dside_accesses[1].dut_access_info.misaligned_second) {
        std::stringstream err_str;
        err_str << "DUT generated first half of misaligned " << iss_action
                << " at address " << std::hex << top_pending_access_info.addr
                << " but second half was expected and not seen";

        errors.emplace_back(err_str.str());

        return kCheckMemCheckFailed;
      }

      // Check the second access had the expected address
      if (pending_dside_accesses[1].dut_access_info.addr !=
          (top_pending_access_info.addr + 4)) {
        std::stringstream err_str;
        err_str << "DUT generated first half of misaligned " << iss_action
                << " at address " << std::hex << top_pending_access_info.addr
                << " but second half had incorrect address "
                << pending_dside_accesses[1].dut_access_info.addr;

        errors.emplace_back(err_str.str());

        return kCheckMemCheckFailed;
      }

      // TODO: How to check BE? May need length of transaction?

      // Remove the top pending access now so both the first and second DUT
      // accesses for this misaligned access are removed.
      pending_dside_accesses.erase(pending_dside_accesses.begin());
    }

    // For any misaligned access that sees an error immediately indicate to
    // spike the error has occured, so ensure the top pending access gets
    // removed.
    pending_access_done = true;
  }

  if (pending_access_done) {
    pending_dside_accesses.erase(pending_dside_accesses.begin());
  }

  return pending_access_error ? kCheckMemBusError : kCheckMemOk;
}

bool SpikeCosim::pc_is_mret(uint32_t pc) {
  uint32_t insn;

  if (!backdoor_read_mem(pc, 4, reinterpret_cast<uint8_t *>(&insn))) {
    return false;
  }

  return insn == 0x30200073;
}

bool SpikeCosim::pc_is_debug_ebreak(uint32_t pc) {
  uint32_t dcsr = processor->get_csr(CSR_DCSR);

  // ebreak debug entry is controlled by the ebreakm (bit 15) and ebreaku (bit
  // 12) fields of DCSR. If the appropriate bit of the current privlege level
  // isn't set ebreak won't enter debug so return false.
  if ((processor->get_state()->prv == PRV_M) && ((dcsr & 0x1000) == 0) ||
      (processor->get_state()->prv == PRV_U) && ((dcsr & 0x8000) == 0)) {
    return false;
  }

  // First check for 16-bit c.ebreak
  uint16_t insn_16;
  if (!backdoor_read_mem(pc, 2, reinterpret_cast<uint8_t *>(&insn_16))) {
    return false;
  }

  if (insn_16 == 0x9002) {
    return true;
  }

  // Not a c.ebreak, check for 32 bit ebreak
  uint32_t insn_32;
  if (!backdoor_read_mem(pc, 4, reinterpret_cast<uint8_t *>(&insn_32))) {
    return false;
  }

  return insn_32 == 0x00100073;
}

bool SpikeCosim::check_debug_ebreak(uint32_t write_reg, uint32_t pc,
                                    bool sync_trap) {
  // A ebreak from the DUT should not write a register and will be reported as a
  // 'sync_trap' (though doesn't act like a trap in various respects).

  if (write_reg != 0) {
    std::stringstream err_str;
    err_str << "DUT executed ebreak at " << std::hex << pc
            << " but also wrote register x" << std::dec << write_reg
            << " which was unexpected";
    errors.emplace_back(err_str.str());

    return false;
  }

  if (sync_trap) {
    std::stringstream err_str;
    err_str << "DUT executed ebreak into debug at " << std::hex << pc
            << " but indicated a synchronous trap, which was unexpected";
    errors.emplace_back(err_str.str());

    return false;
  }

  return true;
}

bool SpikeCosim::pc_is_load(uint32_t pc, uint32_t &rd_out) {
  uint16_t insn_16;

  if (!backdoor_read_mem(pc, 2, reinterpret_cast<uint8_t *>(&insn_16))) {
    return false;
  }

  // C.LW
  if ((insn_16 & 0xE003) == 0x4000) {
    rd_out = ((insn_16 >> 2) & 0x7) + 8;
    return true;
  }

  // C.LWSP
  if ((insn_16 & 0xE003) == 0x4002) {
    rd_out = (insn_16 >> 7) & 0x1F;
    return rd_out != 0;
  }

  uint16_t insn_32;

  if (!backdoor_read_mem(pc, 4, reinterpret_cast<uint8_t *>(&insn_32))) {
    return false;
  }

  // LB/LH/LW/LBU/LHU
  if ((insn_32 & 0x7F) == 0x3) {
    uint32_t func = (insn_32 >> 12) & 0x7;
    if ((func == 0x3) || (func == 0x6) || (func == 0x7)) {
      // Not valid load encodings
      return false;
    }

    rd_out = (insn_32 >> 7) & 0x1F;
    return true;
  }

  return false;
}

unsigned int SpikeCosim::get_insn_cnt() { return insn_cnt; }
