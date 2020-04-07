// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "register_driver.h"
#include "svdpi.h"

#include <map>
#include <string>

#ifdef __cplusplus
extern "C" {
#endif

static std::map<std::string, RegisterDriver *> intfs;

void reg_register_intf(std::string name, RegisterDriver *intf) {
  intfs.insert({name, intf});
}

void reg_deregister_intf(std::string name) { intfs.erase(name); }

void monitor_tick(const char *name, svBit rst_n, svBit illegal_csr,
                  svBit csr_access, const svBitVecVal *csr_op, svBit csr_op_en,
                  const svBitVecVal *csr_addr, const svBitVecVal *csr_wdata,
                  const svBitVecVal *csr_rdata) {
  auto ptr = intfs.find(name);
  if (ptr != intfs.end()) {
    // Send inputs to monitor
    if ((csr_access && (csr_op_en || illegal_csr)) || !rst_n) {
      ptr->second->CaptureTransaction(rst_n, illegal_csr, *csr_op, *csr_addr,
                                      *csr_rdata, *csr_wdata);
    }
  }
}

void driver_tick(const char *name, svBit *csr_access, svBitVecVal *csr_op,
                 svBit *csr_op_en, svBitVecVal *csr_addr,
                 svBitVecVal *csr_wdata) {
  auto ptr = intfs.find(name);
  if (ptr != intfs.end()) {
    // Call OnClock method
    ptr->second->OnClock();
    // Drive outputs
    ptr->second->DriveOutputs(csr_access, csr_op, csr_op_en, csr_addr,
                              csr_wdata);
  }
}

#ifdef __cplusplus
}
#endif
