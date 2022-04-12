// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef SPIKE_COSIM_H_
#define SPIKE_COSIM_H_

#include "cosim.h"
#include "riscv/devices.h"
#include "riscv/log_file.h"
#include "riscv/processor.h"
#include "riscv/simif.h"

#include <stdint.h>
#include <deque>
#include <memory>
#include <string>
#include <vector>

class SpikeCosim : public simif_t, public Cosim {
 private:
  std::unique_ptr<processor_t> processor;
  std::unique_ptr<log_file_t> log;
  bus_t bus;
  std::vector<std::unique_ptr<mem_t>> mems;
  std::vector<std::string> errors;
  bool nmi_mode;

  typedef struct {
    uint8_t mpp;
    bool mpie;
    uint32_t epc;
    uint32_t cause;
  } mstack_t;

  mstack_t mstack;

  void fixup_csr(int csr_num, uint32_t csr_val);

  struct PendingMemAccess {
    DSideAccessInfo dut_access_info;
    uint32_t be_spike;
  };

  std::vector<PendingMemAccess> pending_dside_accesses;

  bool pending_iside_error;
  uint32_t pending_iside_err_addr;

  typedef enum {
    kCheckMemOk,           // Checks passed and access succeded in RTL
    kCheckMemCheckFailed,  // Checks failed
    kCheckMemBusError  // Checks passed, but access generated bus error in RTL
  } check_mem_result_e;

  check_mem_result_e check_mem_access(bool store, uint32_t addr, size_t len,
                                      const uint8_t *bytes);

  bool pc_is_mret(uint32_t pc);

  bool check_gpr_write(const commit_log_reg_t::value_type &reg_change,
                       uint32_t write_reg, uint32_t write_reg_data);

  void on_csr_write(const commit_log_reg_t::value_type &reg_change);

  void leave_nmi_mode();

  int insn_cnt;

 public:
  SpikeCosim(const std::string &isa_string, uint32_t start_pc,
             uint32_t start_mtvec, const std::string &trace_log_path,
             bool secure_ibex, bool icache_en);

  // simif_t implementation
  virtual char *addr_to_mem(reg_t addr) override;
  virtual bool mmio_load(reg_t addr, size_t len, uint8_t *bytes) override;
  virtual bool mmio_store(reg_t addr, size_t len,
                          const uint8_t *bytes) override;
  virtual void proc_reset(unsigned id) override;
  virtual const char *get_symbol(uint64_t addr) override;

  // Cosim implementation
  void add_memory(uint32_t base_addr, size_t size) override;
  bool backdoor_write_mem(uint32_t addr, size_t len,
                          const uint8_t *data_in) override;
  bool backdoor_read_mem(uint32_t addr, size_t len, uint8_t *data_out) override;
  bool step(uint32_t write_reg, uint32_t write_reg_data, uint32_t pc,
            bool sync_trap) override;
  void set_mip(uint32_t mip) override;
  void set_nmi(bool nmi) override;
  void set_debug_req(bool debug_req) override;
  void set_mcycle(uint64_t mcycle) override;
  void notify_dside_access(const DSideAccessInfo &access_info) override;
  // The spike co-simulator assumes iside and dside accesses within a step are
  // disjoint. If both access the same address within a step memory faults may
  // be incorrectly cause on one rather than the other or the access checking
  // will break.
  // TODO: Work on spike changes to remove this restriction
  void set_iside_error(uint32_t addr) override;
  const std::vector<std::string> &get_errors() override;
  void clear_errors() override;
  int get_insn_cnt() override;
};

#endif  // SPIKE_COSIM_H_
