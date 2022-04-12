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

SpikeCosim::SpikeCosim(const std::string &isa_string, uint32_t start_pc,
                       uint32_t start_mtvec, const std::string &trace_log_path,
                       bool secure_ibex, bool icache_en)
    : nmi_mode(false), pending_iside_error(false) {
  FILE *log_file = nullptr;
  if (trace_log_path.length() != 0) {
    log = std::make_unique<log_file_t>(trace_log_path.c_str());
    log_file = log->get();
  }

  processor =
      std::make_unique<processor_t>(isa_string.c_str(), "MU", DEFAULT_VARCH,
                                    this, 0, false, log_file, std::cerr);

  processor->set_ibex_flags(secure_ibex, icache_en);

  processor->set_mmu_capability(IMPL_MMU_SBARE);
  processor->get_state()->pc = start_pc;
  processor->get_state()->mtvec->write(start_mtvec);

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

bool SpikeCosim::step(uint32_t write_reg, uint32_t write_reg_data, uint32_t pc,
                      bool sync_trap) {
  assert(write_reg < 32);

  uint32_t initial_pc = (processor->get_state()->pc & 0xffffffff);
  bool initial_pc_match = initial_pc == pc;

  // Execute the next instruction
  processor->step(1);

  if (processor->get_state()->last_inst_pc == PC_INVALID) {
    if (processor->get_state()->mcause->read() & 0x80000000) {
      // Interrupt occurred, step again to execute first instruction of
      // interrupt
      processor->step(1);
      // TODO: Deal with exception on first instruction of interrupt
      assert(processor->get_state()->last_inst_pc != PC_INVALID);
    } else {
      // Otherwise a synchronous trap has occurred, check the DUT reported a
      // synchronous trap at the same point
      if (!sync_trap) {
        std::stringstream err_str;
        err_str << "Synchronous trap was expected at ISS PC: " << std::hex
                << processor->get_state()->pc
                << " but DUT didn't report one at PC " << pc;
        errors.emplace_back(err_str.str());

        return false;
      }

      if (!initial_pc_match) {
        std::stringstream err_str;
        err_str << "PC mismatch at synchronous trap, DUT: " << std::hex << pc
                << " expected: " << std::hex << initial_pc;
        errors.emplace_back(err_str.str());

        return false;
      }

      if (write_reg != 0) {
        std::stringstream err_str;
        err_str << "Synchronous trap occurred at PC: " << std::hex << pc
                << "but DUT wrote to register: x" << std::dec << write_reg;
        errors.emplace_back(err_str.str());

        return false;
      }

      // Errors may have been generated outside of step() (e.g. in
      // check_mem_access()), return false if there are any.
      return errors.size() == 0;
    }
  }

  // Check PC of executed instruction matches the expected PC
  // TODO: Confirm details of why spike sign extends PC, something to do with
  // 32-bit address as 64-bit address must be sign extended?
  if ((processor->get_state()->last_inst_pc & 0xffffffff) != pc) {
    std::stringstream err_str;
    err_str << "PC mismatch, DUT: " << std::hex << pc
            << " expected: " << std::hex
            << processor->get_state()->last_inst_pc;
    errors.emplace_back(err_str.str());

    return false;
  }

  if (!sync_trap && pc_is_mret(pc) && nmi_mode) {
    // Do handling for recoverable NMI
    leave_nmi_mode();
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

      if (!check_gpr_write(reg_change, write_reg, write_reg_data)) {
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

  if (pending_iside_error) {
    std::stringstream err_str;
    err_str << "DUT generated an iside error for address: " << std::hex
            << pending_iside_err_addr << " but the ISS didn't produce one";
    errors.emplace_back(err_str.str());

    return false;
  }

  pending_iside_error = false;

  // Errors may have been generated outside of step() (e.g. in
  // check_mem_access()). Only increment insn_cnt and return true if there are
  // no errors
  if (errors.size() == 0) {
    insn_cnt++;
    return true;
  }

  return false;
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
  processor->set_csr(CSR_MSTATUS, mstatus);

  processor->set_csr(CSR_MEPC, mstack.epc);
  processor->set_csr(CSR_MCAUSE, mstack.cause);
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

void SpikeCosim::set_debug_req(bool debug_req) {
  processor->halt_request =
      debug_req ? processor_t::HR_REGULAR : processor_t::HR_NONE;
}

void SpikeCosim::set_mcycle(uint64_t mcycle) {
  // TODO: Spike decrements mcycle on write to hack around an issue it has with
  // correctly writing minstret. Preferably this write would use a backdoor
  // access and avoid that decrement but backdoor access isn't part of the
  // public CSR interface.
  processor->get_state()->mcycle->write(mcycle + 1);
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
    case CSR_MSTATUS:
      reg_t mask =
          MSTATUS_MIE | MSTATUS_MPIE | MSTATUS_MPRV | MSTATUS_MPP | MSTATUS_TW;

      reg_t new_val = csr_val & mask;
      processor->set_csr(csr_num, new_val);
      break;
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

int SpikeCosim::get_insn_cnt() { return insn_cnt; }
