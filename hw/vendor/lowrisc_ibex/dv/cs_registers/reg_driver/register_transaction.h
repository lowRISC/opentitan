// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef REGISTER_TRANSACTION_H_
#define REGISTER_TRANSACTION_H_

#include <stdint.h>
#include <random>
#include <string>

// Enumerate the supported register types by macro expansion
enum CSRegisterAddr : int {
#define CSR(reg, addr) kCSR##reg = addr,
#include "csr_listing.def"
};

// Create an indexable array of all CSR addresses
static const uint16_t CSRAddresses[] = {
#define CSR(reg, addr) addr,
#include "csr_listing.def"
};

// Enumerate the four register operation types
enum CSRegisterOperation : int {
  kCSRRead = 0,
  kCSRWrite = 1,
  kCSRSet = 2,
  kCSRClear = 3
};

struct RegisterTransaction {
 public:
  void Randomize(std::default_random_engine &gen);
  void Print();

  CSRegisterOperation csr_op;
  bool illegal_csr;
  uint32_t csr_addr;
  uint32_t csr_rdata;
  uint32_t csr_wdata;

 private:
  std::string RegOpString();
  std::string RegAddrString();
};

#endif  // REGISTER_TRANSACTION_H_
