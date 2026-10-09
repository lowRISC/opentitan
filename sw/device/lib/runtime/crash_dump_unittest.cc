// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * @file
 * @brief Unit tests for the crash-dump utility.
 *
 * ## Test Architecture
 *
 * `crash_dump_capture()` reads four RISC-V CSRs (mepc, mcause, mtval,
 * mstatus) via the `CSR_READ` macro.  On host builds (no `OT_PLATFORM_RV32`)
 * `CSR_READ` calls `mock_csr_read(addr)`, which the `mock_csr` library
 * intercepts via `EXPECT_CSR_READ`.
 *
 * Similarly, the backing store on host builds is a file-static
 * `crash_dump_t g_crash_dump_slot` (compiled into crash_dump.c when
 * `OT_PLATFORM_RV32` is not defined).  `crash_dump_get()` returns a copy of
 * that slot, so the tests can verify the written values without knowing the
 * internal variable name.
 *
 * ## CSR Address Constants Used
 *
 * From sw/device/lib/base/csr_registers.h:
 *   CSR_REG_MEPC    0x341
 *   CSR_REG_MCAUSE  0x342
 *   CSR_REG_MTVAL   0x343
 *   CSR_REG_MSTATUS 0x300
 *
 * The `EXPECT_CSR_READ` helper (from mock_csr.h) programs the next return
 * value for a given CSR address.  The order of `EXPECT_CSR_READ` calls must
 * match the order of `CSR_READ` calls in the implementation.
 *
 * ## Test Suites
 *
 * | Suite                       | What it verifies                            |
 * |-----------------------------|---------------------------------------------|
 * | CrashDumpCaptureTest        | CSR values are serialised correctly         |
 * | CrashDumpReasonTest         | All reason codes are stored faithfully      |
 * | CrashDumpSentinelTest       | Magic sentinel is written last              |
 * | CrashDumpGetTest            | get() returns false when no valid record    |
 * | CrashDumpClearTest          | clear() invalidates the record              |
 * | CrashDumpRoundTripTest      | capture → get → clear → get round-trip     |
 * | CrashDumpWatchdogScenario   | Primary scenario: watchdog NMI captures PC |
 * | CrashDumpExceptionScenario  | Primary scenario: illegal-instr exception   |
 */

#include "sw/device/lib/runtime/crash_dump.h"

#include <cstring>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_csr.h"

// CSR addresses — must match csr_registers.h.
#include "sw/device/lib/base/csr_registers.h"

namespace crash_dump_unittest {
namespace {

using ::mock_csr::MockCsr;
using ::testing::InSequence;

// ---------------------------------------------------------------------------
// Helper: programme the four CSR reads in implementation order.
//
// The implementation reads: mepc, mcause, mtval, mstatus (in that order).
// ---------------------------------------------------------------------------
void ExpectCsrCapture(uint32_t mepc, uint32_t mcause, uint32_t mtval,
                      uint32_t mstatus) {
  InSequence seq;
  EXPECT_CSR_READ(CSR_REG_MEPC, mepc);
  EXPECT_CSR_READ(CSR_REG_MCAUSE, mcause);
  EXPECT_CSR_READ(CSR_REG_MTVAL, mtval);
  EXPECT_CSR_READ(CSR_REG_MSTATUS, mstatus);
}

// ---------------------------------------------------------------------------
// Base fixture: each test starts with a clean slate.
// ---------------------------------------------------------------------------
class CrashDumpTest : public ::testing::Test {
 protected:
  void SetUp() override {
    // Erase any record left by a previous test.
    crash_dump_clear();
  }
};

// ---------------------------------------------------------------------------
// Suite 1: Core capture-and-readback correctness.
// ---------------------------------------------------------------------------
class CrashDumpCaptureTest : public CrashDumpTest {};

TEST_F(CrashDumpCaptureTest, CsrValuesAreStoredCorrectly) {
  constexpr uint32_t kMepc = 0x2000'1234u;
  constexpr uint32_t kMcause = 0x0000'0005u;  // Load access fault.
  constexpr uint32_t kMtval = 0xDEAD'BEEFu;
  constexpr uint32_t kMstatus = 0x0000'1880u;  // MIE=0, MPIE=1, MPP=11.

  ExpectCsrCapture(kMepc, kMcause, kMtval, kMstatus);
  crash_dump_capture(kCrashDumpReasonException);

  crash_dump_t dump;
  ASSERT_TRUE(crash_dump_get(&dump));

  EXPECT_EQ(dump.magic, static_cast<uint32_t>(kCrashDumpMagic));
  EXPECT_EQ(dump.reason, static_cast<uint32_t>(kCrashDumpReasonException));
  EXPECT_EQ(dump.mepc, kMepc);
  EXPECT_EQ(dump.mcause, kMcause);
  EXPECT_EQ(dump.mtval, kMtval);
  EXPECT_EQ(dump.mstatus, kMstatus);
}

TEST_F(CrashDumpCaptureTest, AllZeroCsrsAreStoredCorrectly) {
  ExpectCsrCapture(0u, 0u, 0u, 0u);
  crash_dump_capture(kCrashDumpReasonManual);

  crash_dump_t dump;
  ASSERT_TRUE(crash_dump_get(&dump));
  EXPECT_EQ(dump.mepc, 0u);
  EXPECT_EQ(dump.mcause, 0u);
  EXPECT_EQ(dump.mtval, 0u);
  EXPECT_EQ(dump.mstatus, 0u);
}

TEST_F(CrashDumpCaptureTest, AllOnesCsrsAreStoredCorrectly) {
  ExpectCsrCapture(0xFFFF'FFFFu, 0xFFFF'FFFFu, 0xFFFF'FFFFu, 0xFFFF'FFFFu);
  crash_dump_capture(kCrashDumpReasonWatchdog);

  crash_dump_t dump;
  ASSERT_TRUE(crash_dump_get(&dump));
  EXPECT_EQ(dump.mepc, 0xFFFF'FFFFu);
  EXPECT_EQ(dump.mcause, 0xFFFF'FFFFu);
  EXPECT_EQ(dump.mtval, 0xFFFF'FFFFu);
  EXPECT_EQ(dump.mstatus, 0xFFFF'FFFFu);
}

TEST_F(CrashDumpCaptureTest, SecondCaptureOverwritesFirst) {
  // First capture with mepc=0x1000.
  ExpectCsrCapture(0x1000u, 0u, 0u, 0u);
  crash_dump_capture(kCrashDumpReasonException);

  // Second capture with mepc=0x2000 overwrites.
  ExpectCsrCapture(0x2000u, 0u, 0u, 0u);
  crash_dump_capture(kCrashDumpReasonWatchdog);

  crash_dump_t dump;
  ASSERT_TRUE(crash_dump_get(&dump));
  EXPECT_EQ(dump.mepc, 0x2000u);
  EXPECT_EQ(dump.reason, static_cast<uint32_t>(kCrashDumpReasonWatchdog));
}

// ---------------------------------------------------------------------------
// Suite 2: Reason codes are stored faithfully.
// ---------------------------------------------------------------------------
class CrashDumpReasonTest : public CrashDumpTest,
                            public ::testing::WithParamInterface<
                                crash_dump_reason_t> {};

TEST_P(CrashDumpReasonTest, ReasonCodeIsPreserved) {
  crash_dump_reason_t reason = GetParam();
  ExpectCsrCapture(0u, 0u, 0u, 0u);
  crash_dump_capture(reason);

  crash_dump_t dump;
  ASSERT_TRUE(crash_dump_get(&dump));
  EXPECT_EQ(dump.reason, static_cast<uint32_t>(reason));
}

INSTANTIATE_TEST_SUITE_P(AllReasonCodes, CrashDumpReasonTest,
                         ::testing::Values(kCrashDumpReasonNone,
                                           kCrashDumpReasonWatchdog,
                                           kCrashDumpReasonException,
                                           kCrashDumpReasonManual));

// ---------------------------------------------------------------------------
// Suite 3: Magic sentinel correctness.
// ---------------------------------------------------------------------------
class CrashDumpSentinelTest : public CrashDumpTest {};

TEST_F(CrashDumpSentinelTest, MagicMatchesConstantAfterCapture) {
  ExpectCsrCapture(0u, 0u, 0u, 0u);
  crash_dump_capture(kCrashDumpReasonManual);

  crash_dump_t dump;
  ASSERT_TRUE(crash_dump_get(&dump));
  EXPECT_EQ(dump.magic, static_cast<uint32_t>(kCrashDumpMagic));
}

// ---------------------------------------------------------------------------
// Suite 4: crash_dump_get() before any capture.
// ---------------------------------------------------------------------------
class CrashDumpGetTest : public ::testing::Test {};

TEST_F(CrashDumpGetTest, ReturnsFalseWhenNoRecord) {
  // Ensure there is no valid record (clear without priming a capture).
  crash_dump_clear();

  crash_dump_t dump;
  // Poison the output; get() must leave it unmodified when returning false.
  std::memset(&dump, 0xAB, sizeof(dump));
  const uint32_t kPoisonWord = 0xABABABABu;

  EXPECT_FALSE(crash_dump_get(&dump));
  // Output must be unchanged (we check one field as a proxy for the rest).
  EXPECT_EQ(dump.mepc, kPoisonWord);
}

// ---------------------------------------------------------------------------
// Suite 5: crash_dump_clear().
// ---------------------------------------------------------------------------
class CrashDumpClearTest : public CrashDumpTest {};

TEST_F(CrashDumpClearTest, ClearInvalidatesRecord) {
  // Write a record.
  ExpectCsrCapture(0x4000u, 0u, 0u, 0u);
  crash_dump_capture(kCrashDumpReasonException);

  crash_dump_t dump;
  ASSERT_TRUE(crash_dump_get(&dump));  // Verify it was written.

  // Clear it.
  crash_dump_clear();

  // get() must now return false.
  EXPECT_FALSE(crash_dump_get(&dump));
}

TEST_F(CrashDumpClearTest, DoubleClearIsIdempotent) {
  crash_dump_clear();
  crash_dump_clear();  // Should not crash or corrupt anything.
  crash_dump_t dump;
  EXPECT_FALSE(crash_dump_get(&dump));
}

// ---------------------------------------------------------------------------
// Suite 6: Round-trip: capture → get → clear → get.
// ---------------------------------------------------------------------------
class CrashDumpRoundTripTest : public ::testing::Test {};

TEST_F(CrashDumpRoundTripTest, RoundTrip) {
  crash_dump_clear();

  constexpr uint32_t kMepc = 0x2000'ABCD;
  constexpr uint32_t kMcause = 0x0000'0002u;  // Illegal instruction.
  constexpr uint32_t kMtval = 0x0000'1234u;   // Instruction word.
  constexpr uint32_t kMstatus = 0x0000'0088u;

  ExpectCsrCapture(kMepc, kMcause, kMtval, kMstatus);
  crash_dump_capture(kCrashDumpReasonException);

  // Phase 1: get returns true.
  crash_dump_t dump1;
  ASSERT_TRUE(crash_dump_get(&dump1));
  EXPECT_EQ(dump1.mepc, kMepc);
  EXPECT_EQ(dump1.mcause, kMcause);
  EXPECT_EQ(dump1.mtval, kMtval);
  EXPECT_EQ(dump1.mstatus, kMstatus);
  EXPECT_EQ(dump1.reason, static_cast<uint32_t>(kCrashDumpReasonException));

  // Phase 2: clear.
  crash_dump_clear();

  // Phase 3: get returns false.
  crash_dump_t dump2;
  EXPECT_FALSE(crash_dump_get(&dump2));
}

// ---------------------------------------------------------------------------
// Suite 7: Primary scenario — watchdog-bite NMI captures the interrupted PC.
//
// This reproduces the most common field-debuggability scenario:
//   - Firmware is stuck in an infinite loop at PC 0x2000_0050.
//   - The AON watchdog fires a bite NMI.
//   - The NMI handler calls crash_dump_capture(kCrashDumpReasonWatchdog).
//   - mepc holds the PC of the looping instruction.
//   - mcause encodes the machine NMI (bit31=1, cause=0x1f on Ibex).
// ---------------------------------------------------------------------------
class CrashDumpWatchdogScenario : public CrashDumpTest {};

TEST_F(CrashDumpWatchdogScenario, WatchdogNmiPreservesLoopPc) {
  // Simulated hardware state at NMI entry:
  //   mepc    = 0x2000_0050  (PC of the looping instruction)
  //   mcause  = 0x8000_001F  (machine NMI, Ibex watchdog bark)
  //   mtval   = 0x0000_0000  (no auxiliary information for NMI)
  //   mstatus = 0x0000_0088  (MPIE=1, MPP=11 i.e. was in M-mode)
  constexpr uint32_t kLoopPc = 0x2000'0050u;
  constexpr uint32_t kWdogNmi = 0x8000'001Fu;
  constexpr uint32_t kNoMtval = 0x0000'0000u;
  constexpr uint32_t kMstatus = 0x0000'0088u;

  ExpectCsrCapture(kLoopPc, kWdogNmi, kNoMtval, kMstatus);
  crash_dump_capture(kCrashDumpReasonWatchdog);

  crash_dump_t dump;
  ASSERT_TRUE(crash_dump_get(&dump))
      << "Watchdog NMI handler must produce a valid dump";
  EXPECT_EQ(dump.reason, static_cast<uint32_t>(kCrashDumpReasonWatchdog))
      << "Reason code must identify a watchdog capture";
  EXPECT_EQ(dump.mepc, kLoopPc)
      << "mepc must hold the PC of the interrupted (looping) instruction";
  EXPECT_EQ(dump.mcause, kWdogNmi)
      << "mcause must encode the NMI cause";
  EXPECT_EQ(dump.mtval, kNoMtval);
  EXPECT_EQ(dump.mstatus, kMstatus);
}

// ---------------------------------------------------------------------------
// Suite 8: Primary scenario — illegal-instruction exception.
//
//   - Firmware fetches an undefined 32-bit opcode at PC 0x2000_AB00.
//   - Ibex raises an illegal-instruction exception.
//   - mepc = 0x2000_AB00, mcause = 0x2 (illegal instruction),
//     mtval = the faulting instruction word.
// ---------------------------------------------------------------------------
class CrashDumpExceptionScenario : public CrashDumpTest {};

TEST_F(CrashDumpExceptionScenario, IllegalInstructionExceptionCapture) {
  constexpr uint32_t kFaultPc = 0x2000'AB00u;
  constexpr uint32_t kIllegalInstr = 0x0000'0002u;  // mcause: illegal instr.
  constexpr uint32_t kBadInstrWord = 0xDEAD'C0DEu;  // the offending instr.
  constexpr uint32_t kMstatus = 0x0000'1808u;

  ExpectCsrCapture(kFaultPc, kIllegalInstr, kBadInstrWord, kMstatus);
  crash_dump_capture(kCrashDumpReasonException);

  crash_dump_t dump;
  ASSERT_TRUE(crash_dump_get(&dump))
      << "Exception handler must produce a valid dump";
  EXPECT_EQ(dump.reason, static_cast<uint32_t>(kCrashDumpReasonException));
  EXPECT_EQ(dump.mepc, kFaultPc)
      << "mepc must hold the PC of the faulting instruction";
  EXPECT_EQ(dump.mcause, kIllegalInstr)
      << "mcause must encode 'illegal instruction'";
  EXPECT_EQ(dump.mtval, kBadInstrWord)
      << "mtval must hold the offending instruction word";
}

TEST_F(CrashDumpExceptionScenario, LoadAccessFaultCapture) {
  constexpr uint32_t kFaultPc = 0x2000'10F8u;
  constexpr uint32_t kLoadFault = 0x0000'0005u;  // mcause: load access fault.
  constexpr uint32_t kBadAddr = 0x1000'0004u;    // address causing the fault.
  constexpr uint32_t kMstatus = 0x0000'1808u;

  ExpectCsrCapture(kFaultPc, kLoadFault, kBadAddr, kMstatus);
  crash_dump_capture(kCrashDumpReasonException);

  crash_dump_t dump;
  ASSERT_TRUE(crash_dump_get(&dump));
  EXPECT_EQ(dump.mcause, kLoadFault);
  EXPECT_EQ(dump.mtval, kBadAddr)
      << "mtval must hold the faulting load address";
}

}  // namespace
}  // namespace crash_dump_unittest
