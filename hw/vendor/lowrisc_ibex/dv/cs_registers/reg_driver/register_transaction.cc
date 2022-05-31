// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "register_transaction.h"

#include <iostream>

void RegisterTransaction::Randomize(std::default_random_engine &gen) {
  std::uniform_int_distribution<int> addr_dist_ =
      std::uniform_int_distribution<int>(
          0, (sizeof(CSRAddresses) / sizeof(uint16_t)) - 1);
  std::uniform_int_distribution<int> wdata_dist_ =
      std::uniform_int_distribution<int>(0, 0xFFFFFFFF);
  std::uniform_int_distribution<int> operation_dist_ =
      std::uniform_int_distribution<int>(kCSRRead, kCSRClear);
  // Generate a random array index, and get the address
  csr_addr = CSRAddresses[addr_dist_(gen)];
  // Generate a random op type
  csr_op = static_cast<CSRegisterOperation>(operation_dist_(gen));
  if (csr_op != kCSRRead) {
    // Generate random wdata
    csr_wdata = wdata_dist_(gen);
  }
}

void RegisterTransaction::Print() {
  std::cout << "Register transaction:" << std::endl
            << "Operation:  " << RegOpString() << std::endl
            << "Address:    " << RegAddrString() << std::endl;
  if (csr_op != kCSRRead) {
    std::cout << "Write data: " << std::hex << csr_wdata << std::endl;
  }
  std::cout << "Read data:  " << std::hex << csr_rdata << std::dec << std::endl;
}

std::string RegisterTransaction::RegOpString() {
  switch (csr_op) {
    case kCSRRead:
      return "CSR Read";
    case kCSRWrite:
      return "CSR Write";
    case kCSRSet:
      return "CSR Set";
    case kCSRClear:
      return "CSR Clear";
    default:
      return "Unknown op";
  }
}

std::string RegisterTransaction::RegAddrString() {
  // String representation created automatically by macro
  switch (csr_addr) {
#define CSR(reg, addr) \
  case kCSR##reg:      \
    return #reg;
#include "csr_listing.def"
    default:
      return "Undef reg: " + std::to_string(csr_addr);
  }
}
