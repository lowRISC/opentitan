// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef COSIM_DPI_H_
#define COSIM_DPI_H_

#include <stdint.h>
#include <svdpi.h>

// This adapts the C++ interface of the `Cosim` class to be used via DPI. See
// the documentation in cosim.h for further details

extern "C" {
int riscv_cosim_step(Cosim *cosim, const svBitVecVal *write_reg,
                     const svBitVecVal *write_reg_data, const svBitVecVal *pc,
                     svBit sync_trap, svBit suppress_reg_write);
void riscv_cosim_set_mip(Cosim *cosim, const svBitVecVal *mip);
void riscv_cosim_set_nmi(Cosim *cosim, svBit nmi);
void riscv_cosim_set_nmi_int(Cosim *cosim, svBit nmi_int);
void riscv_cosim_set_debug_req(Cosim *cosim, svBit debug_req);
void riscv_cosim_set_mcycle(Cosim *cosim, svBitVecVal *mcycle);
void riscv_cosim_set_csr(Cosim *cosim, const int csr_id,
                         const svBitVecVal *csr_val);
void riscv_cosim_set_ic_scr_key_valid(Cosim *cosim, svBit valid);
void riscv_cosim_notify_dside_access(Cosim *cosim, svBit store,
                                     svBitVecVal *addr, svBitVecVal *data,
                                     svBitVecVal *be, svBit error,
                                     svBit misaligned_first,
                                     svBit misaligned_second);
void riscv_cosim_set_iside_error(Cosim *cosim, svBitVecVal *addr);
int riscv_cosim_get_num_errors(Cosim *cosim);
const char *riscv_cosim_get_error(Cosim *cosim, int index);
void riscv_cosim_clear_errors(Cosim *cosim);
void riscv_cosim_write_mem_byte(Cosim *cosim, const svBitVecVal *addr,
                                const svBitVecVal *d);
unsigned int riscv_cosim_get_insn_cnt(Cosim *cosim);
}

#endif  // COSIM_DPI_H_
