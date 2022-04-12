// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <string>
#include <vector>

#ifndef COSIM_H_
#define COSIM_H_

// Information about a dside transaction observed on the DUT memory interface
struct DSideAccessInfo {
  // set when the access is a store, in which case `data` is the store data from
  // the DUT. Otherwise `data` is the load data provided to the DUT.
  bool store;
  // `addr` is the address and must be 32-bit aligned. `data` and `be` are
  // aligned to the address. For example an 8-bit store of 0xff to 0x12 has
  // `data` as 0x00ff0000, `addr` as 0x10 and `be` as 0b0100.
  uint32_t data;
  uint32_t addr;
  uint32_t be;

  // set if an error response to the transaction is seen.
  bool error;

  // `misaligned_first` and `misaligned_second` are set when the transaction is
  // generated for a misaligned store or load instruction.  `misaligned_first`
  // is true when the transaction is for the lower half and `misaligned_second`
  // is true when the transaction is for the upper half, if it exists.
  //
  // For example an unaligned 32-bit load to 0x3 produces a transaction with
  // `addr` as 0x0 and `misaligned_first` set to true, then a transaction with
  // `addr` as 0x4 and `misaligned_second` set to true. An unaligned 16-bit load
  // to 0x01 only produces a transaction with `addr` as 0x0 and
  // `misaligned_first` set to true, there is no second half.
  bool misaligned_first;
  bool misaligned_second;
};

class Cosim {
 public:
  virtual ~Cosim() {}

  // Add a memory to the co-simulator environment.
  //
  // Use `backdoor_write_mem`/`backdoor_read_mem` to access it from the
  // simulation environment.
  virtual void add_memory(uint32_t base_addr, size_t size) = 0;

  // Write bytes to co-simulator memory.
  //
  // returns false if write fails (e.g. because no memory exists at the bytes
  // being written).
  virtual bool backdoor_write_mem(uint32_t addr, size_t len,
                                  const uint8_t *data_in) = 0;

  // Read bytes from co-simulator memory.
  //
  // returns false if read fails (e.g. because no memory exists at the bytes
  // being read).
  virtual bool backdoor_read_mem(uint32_t addr, size_t len,
                                 uint8_t *data_out) = 0;

  // Step the co-simulator, checking register write and PC of executed
  // instruction match the supplied values. `write_reg` gives the index of the
  // written register along with `write_reg_data` which provides the data. A
  // `write_reg` of 0 indicates no register write occurred.
  //
  // `sync_trap` is set to true when the instruction caused a synchronous trap.
  // In this case the instruction doesn't retire so no register write occurs (so
  // `write_reg` must be 0).
  //
  // Returns false if there are any errors; use `get_errors` to obtain details
  virtual bool step(uint32_t write_reg, uint32_t write_reg_data, uint32_t pc,
                    bool sync_trap) = 0;

  // When more than one of `set_mip`, `set_nmi` or `set_debug_req` is called
  // before `step` which one takes effect is chosen by the co-simulator. Which
  // should take priority is architecturally defined by the RISC-V
  // specification.

  // Set the value of MIP.
  //
  // At the next call of `step`, the MIP value will take effect (i.e. if it's a
  // new interrupt that is enabled it will step straight to that handler).
  virtual void set_mip(uint32_t mip) = 0;

  // Set the state of the NMI (non-maskable interrupt) line.
  //
  // The NMI signal is a level triggered interrupt. When the NMI is taken the
  // CPU ignores the NMI line until an `mret` instruction is executed. If the
  // NMI is high following the `mret` (regardless of whether it has been low or
  // not whilst the first NMI is being handled) a new NMI is taken.
  //
  // When an NMI is due to be taken that will occur at the next call of `step`.
  virtual void set_nmi(bool nmi) = 0;

  // Set the debug request.
  //
  // When set to true the core will enter debug mode at the next step
  virtual void set_debug_req(bool debug_req) = 0;

  // Set the value of mcycle.
  //
  // The co-simulation model doesn't alter the value of mcycle itself (other
  // than instructions that do a direct CSR write). mcycle should be set to the
  // correct value before any `step` call that may execute an instruction that
  // observes the value of mcycle.
  //
  // A full 64-bit value is provided setting both the mcycle and mcycleh CSRs.
  virtual void set_mcycle(uint64_t mcycle) = 0;

  // Tell the co-simulation model about observed transactions on the dside
  // memory interface of the DUT. Accesses are notified once the response to a
  // transaction is seen.
  //
  // Observed transactions for the DUT are checked against accesses from the
  // co-simulation model when a memory access occurs during a `step`. If there
  // is a mismatch an error is reported which can be obtained via `get_errors`.
  virtual void notify_dside_access(const DSideAccessInfo &access_info) = 0;

  // Tell the co-simulation model about an error response to an iside fetch.
  //
  // `addr` must be 32-bit aligned.
  //
  // The next step following a call to `set_iside_error` must produce an
  // instruction fault at the given address.
  virtual void set_iside_error(uint32_t addr) = 0;

  // Get a vector of strings describing errors that have occurred during `step`
  virtual const std::vector<std::string> &get_errors() = 0;

  // Clear internal vector of error descriptions
  virtual void clear_errors() = 0;

  // Returns a count of instructions executed by co-simulator and DUT without
  // failures.
  virtual int get_insn_cnt() = 0;
};

#endif  // COSIM_H_
