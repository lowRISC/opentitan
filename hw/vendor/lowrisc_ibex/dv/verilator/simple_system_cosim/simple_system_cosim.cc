// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <svdpi.h>
#include <cassert>
#include <memory>
#include "cosim.h"
#include "ibex_simple_system.h"
#include "spike_cosim.h"
#include "verilator_memutil.h"

class SimpleSystemCosim : public SimpleSystem {
 public:
  std::unique_ptr<SpikeCosim> _cosim;

  SimpleSystemCosim(const char *ram_hier_path, int ram_size_words)
      : SimpleSystem(ram_hier_path, ram_size_words), _cosim(nullptr) {}

  ~SimpleSystemCosim() {}

  void CreateCosim(bool secure_ibex, bool icache_en, uint32_t pmp_num_regions,
                   uint32_t pmp_granularity, uint32_t mhpm_counter_num) {
    _cosim = std::make_unique<SpikeCosim>(
        GetIsaString(), 0x100080, 0x100001, "simple_system_cosim.log",
        secure_ibex, icache_en, pmp_num_regions, pmp_granularity,
        mhpm_counter_num);

    _cosim->add_memory(0x100000, 1024 * 1024);
    _cosim->add_memory(0x20000, 4096);

    CopyMemAreaToCosim(&_ram, 0x100000);
  }

 protected:
  void CopyMemAreaToCosim(MemArea *area, uint32_t base_addr) {
    auto mem_data = area->Read(0, area->GetSizeWords());
    _cosim->backdoor_write_mem(base_addr, area->GetSizeBytes(), &mem_data[0]);
  }

  virtual int Setup(int argc, char **argv, bool &exit_app) override {
    int ret_code = SimpleSystem::Setup(argc, argv, exit_app);
    if (exit_app) {
      return ret_code;
    }

    return 0;
  }

  virtual bool Finish() {
    std::cout << "Co-simulation matched " << _cosim->get_insn_cnt()
              << " instructions\n";

    return SimpleSystem::Finish();
  }
};

// Use raw pointer as destruction outside main can cause segment fault (due to
// undefined instruction order vs VerilatorSimCtrl singleton).
SimpleSystemCosim *simple_system_cosim;

extern "C" {
void *get_spike_cosim() {
  assert(simple_system_cosim);
  assert(simple_system_cosim->_cosim);

  return static_cast<Cosim *>(simple_system_cosim->_cosim.get());
}

void create_cosim(svBit secure_ibex, svBit icache_en,
                  const svBitVecVal *pmp_num_regions,
                  const svBitVecVal *pmp_granularity,
                  const svBitVecVal *mhpm_counter_num) {
  assert(simple_system_cosim);
  simple_system_cosim->CreateCosim(secure_ibex, icache_en, pmp_num_regions[0],
                                   pmp_granularity[0], mhpm_counter_num[0]);
}
}

int main(int argc, char **argv) {
  simple_system_cosim = new SimpleSystemCosim(
      "TOP.ibex_simple_system.u_ram.u_ram.gen_generic.u_impl_generic",
      (1024 * 1024) / 4);

  int ret_code = simple_system_cosim->Main(argc, argv);

  delete simple_system_cosim;

  return ret_code;
}
