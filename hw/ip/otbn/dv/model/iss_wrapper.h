// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_HW_IP_OTBN_DV_MODEL_ISS_WRAPPER_H_
#define OPENTITAN_HW_IP_OTBN_DV_MODEL_ISS_WRAPPER_H_

#include <array>
#include <cstdint>
#include <cstdio>
#include <memory>
#include <string>
#include <unistd.h>
#include <vector>

// Forward declaration (the implementation is private in iss_wrapper.cc)
struct TmpDir;

// OTBN has some externally visible CSRs that can be updated by hardware
// (without explicit writes from software). The ISSWrapper mirrors the ISS's
// versions of these registers in this structure.
class MirroredRegs {
 public:
  MirroredRegs()
      : status(0),
        insn_cnt(0),
        err_bits(0),
        stop_pc(0),
        rnd_req(false),
        wipe_start(false) {}

  uint32_t status;
  uint32_t insn_cnt;
  uint32_t err_bits;

  // The final PC from the most recent run
  uint32_t stop_pc;

  // We are issuing an EDN request for RND
  bool rnd_req;

  // This goes high for a single cycle when we start the internal secure wipe
  // (and can be used as a trigger to check internal state before it gets
  // trashed)
  bool wipe_start;

  // Execution is stopped if status is either 0 (IDLE) or 0xff (LOCKED)
  bool stopped() const { return status == 0 || status == 0xff; }
};

// An object wrapping the ISS subprocess.
struct ISSWrapper {
  // A 256-bit unsigned integer value, stored in "LSB order". Thus, words[0]
  // contains the LSB and words[7] contains the MSB.
  struct u256_t {
    uint32_t words[256 / 32];
  };

  ISSWrapper(bool enable_secure_wipe);
  ~ISSWrapper();

  // Load new contents of DMEM / IMEM
  void load_d(const std::string &path);
  void load_i(const std::string &path);

  // Add a loop warp instruction to the simulation
  void add_loop_warp(uint32_t addr, uint32_t from_cnt, uint32_t to_cnt);

  // Clear any loop warp instructions from the simulation
  void clear_loop_warps();

  // Dump the contents of DMEM to a file
  void dump_d(const std::string &path) const;

  // Jump to address zero and start running
  void start();

  // Start DMEM Secure wipe operation, set status accordingly
  void dmem_wipe();

  // Start IMEM Secure wipe operation, set status accordingly
  void imem_wipe();

  // Flush EDN related content in model because of edn_rst_n
  void edn_flush();

  // Provide data for RND. ISS will stall when RND is read and RND data isn't
  // available. RND data is available only when 8 32b packages are sent and
  // also RTL signals CDC is done.
  void edn_rnd_step(uint32_t edn_rnd_data);

  // Provide data for URND seed. ISS will stall until reseeding of URND is
  // complete. URND seed data is available only when 8 32b packages are sent and
  // also RTL signals CDC is done.
  void edn_urnd_step(uint32_t edn_urnd_data);

  // Provide keymgr values to model
  void set_keymgr_value(const std::array<uint32_t, 12> &key0_arr,
                        const std::array<uint32_t, 12> &key1_arr, bool valid);

  // Signals that the received OTP key is valid in the RTL.
  void otp_key_cdc_done();

  // Signals 256b EDN random number for RND is valid in the RTL.
  void edn_rnd_cdc_done();

  // Signals 256b EDN random number for URND seed is valid in the RTL.
  void edn_urnd_cdc_done();

  // Run simulation for a single cycle.
  //
  // If gen_trace is true, pass trace data to the (singleton) OtbnTraceChecker
  // object.
  //
  // The return code describes the state of the simulation. It is 1 if the
  // simulation just stopped (on ECALL or an architectural error); it is 0 if
  // the simulation is still running. It is -1 if something went wrong (such as
  // a trace mismatch).
  //
  // Updates mirrored versions of STATUS and INSN_CNT registers. If execution
  // finishes (so we return 1), also updates mirrored versions of ERR_BITS and
  // the final PC (see get_stop_pc()).
  int step(bool gen_trace);

  // Mark all of IMEM as invalid so that any fetch causes an integrity error.
  void invalidate_imem();

  // Mark all of DMEM as invalid so that any load causes an integrity error.
  void invalidate_dmem();

  // Step a CRC calculation with 48 bits of data
  uint32_t step_crc(const std::array<uint8_t, 6> &item, uint32_t state) const;

  // Reset simulation
  //
  // This doesn't actually send anything to the ISS, but instead tells the
  // OtbnTraceChecker to clear out any partial instructions. It also resets
  // mirrored registers to their initial states.
  void reset(bool gen_trace);

  // Send a lifecycle controller escalation signal
  void send_lc_escalation();

  const MirroredRegs &get_mirrored() const { return mirrored_; }

  // Read contents of the register file
  void get_regs(std::array<uint32_t, 32> *gprs, std::array<u256_t, 32> *wdrs);

  // Read the contents of the call stack
  std::vector<uint32_t> get_call_stack();

  // Resolve a path relative to the convenience temporary directory.
  // relative should be a relative path (it is just appended to the
  // path of the temporary directory).
  std::string make_tmp_path(const std::string &relative) const;

 private:
  // Read line by line from the child process until we get ".\n".
  // Return true if we got the ".\n" terminator, false if EOF. If dst
  // is not null, append to it each line that was read.
  bool read_child_response(std::vector<std::string> *dst) const;

  // Send a command to the child and wait for its response. If no
  // response, raise a runtime_error.
  void run_command(const std::string &cmd, std::vector<std::string> *dst) const;

  pid_t child_pid;
  FILE *child_write_file;
  FILE *child_read_file;

  // A temporary directory for communicating with the child process
  std::unique_ptr<TmpDir> tmpdir;

  bool enable_secure_wipe;

  // Mirrored copies of registers
  MirroredRegs mirrored_;
};

#endif  // OPENTITAN_HW_IP_OTBN_DV_MODEL_ISS_WRAPPER_H_
