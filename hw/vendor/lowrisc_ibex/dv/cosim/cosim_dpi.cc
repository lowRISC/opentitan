// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <svdpi.h>
#include <cassert>

#include "cosim.h"
#include "cosim_dpi.h"

int riscv_cosim_step(Cosim *cosim, const svBitVecVal *write_reg,
                     const svBitVecVal *write_reg_data, const svBitVecVal *pc,
                     svBit sync_trap) {
  assert(cosim);

  return cosim->step(write_reg[0], write_reg_data[0], pc[0], sync_trap) ? 1 : 0;
}

void riscv_cosim_set_mip(Cosim *cosim, const svBitVecVal *mip) {
  assert(cosim);

  cosim->set_mip(mip[0]);
}

void riscv_cosim_set_nmi(Cosim *cosim, svBit nmi) {
  assert(cosim);

  cosim->set_nmi(nmi);
}

void riscv_cosim_set_debug_req(Cosim *cosim, svBit debug_req) {
  assert(cosim);

  cosim->set_debug_req(debug_req);
}

void riscv_cosim_set_mcycle(Cosim *cosim, svBitVecVal *mcycle) {
  assert(cosim);

  uint64_t mcycle_full = mcycle[0] | (uint64_t)mcycle[1] << 32;
  cosim->set_mcycle(mcycle_full);
}

void riscv_cosim_notify_dside_access(Cosim *cosim, svBit store,
                                     svBitVecVal *addr, svBitVecVal *data,
                                     svBitVecVal *be, svBit error,
                                     svBit misaligned_first,
                                     svBit misaligned_second) {
  assert(cosim);

  cosim->notify_dside_access(
      DSideAccessInfo{.store = store != 0,
                      .data = data[0],
                      .addr = addr[0],
                      .be = be[0],
                      .error = error != 0,
                      .misaligned_first = misaligned_first != 0,
                      .misaligned_second = misaligned_second != 0});
}

void riscv_cosim_set_iside_error(Cosim *cosim, svBitVecVal *addr) {
  assert(cosim);

  cosim->set_iside_error(addr[0]);
}

int riscv_cosim_get_num_errors(Cosim *cosim) {
  assert(cosim);

  return cosim->get_errors().size();
}

const char *riscv_cosim_get_error(Cosim *cosim, int index) {
  assert(cosim);

  if (index >= cosim->get_errors().size()) {
    return nullptr;
  }

  return cosim->get_errors()[index].c_str();
}

void riscv_cosim_clear_errors(Cosim *cosim) {
  assert(cosim);

  cosim->clear_errors();
}

void riscv_cosim_write_mem_byte(Cosim *cosim, const svBitVecVal *addr,
                                const svBitVecVal *d) {
  assert(cosim);
  uint8_t byte = d[0] & 0xff;
  cosim->backdoor_write_mem(addr[0], 1, &byte);
}

int riscv_cosim_get_insn_cnt(Cosim *cosim) {
  assert(cosim);

  return cosim->get_insn_cnt();
}
