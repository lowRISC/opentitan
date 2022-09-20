// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <array>
#include <cstring>
#include <vector>

#include "gtest/gtest.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/silicon_creator/lib/base/mock_csr.h"
#include "sw/device/silicon_creator/lib/epmp_state.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace epmp_unittest {
namespace {

/**
 * Representation of the hardware PMP control register state.
 */
struct PmpCsrs {
  /**
   * The unpacked PMP configuration (`pmpNcfg`) registers, one entry for each
   * PMP entry.
   */
  std::array<uint8_t, kEpmpNumRegions> pmpcfg = {};

  /**
   * The PMP address registers, one for each PMP entry.
   */
  std::array<uint32_t, kEpmpNumRegions> pmpaddr = {};

  /**
   * The Machine Security Configuration register.
   */
  uint64_t mseccfg = 0;

  /**
   * Pack the individual (`pmpNcfg`) PMP entry configuration register
   * values into hardware register (`pmpcfgN`) values.
   *
   * @returns An array representing the packed `pmpcfgN` values.
   */
  std::array<uint32_t, kEpmpNumRegions / 4> PackCfg() const {
    // There are four 8-bit `pmpNcfg` values packed into each `pmpcfgN`
    // register.
    std::array<uint32_t, kEpmpNumRegions / 4> packed;
    std::memcpy(&packed, &pmpcfg, sizeof(pmpcfg));
    return packed;
  }

  /**
   * Generate a state that is a snapshot of the current PMP control register
   * values.
   *
   * @returns An `epmp_state_t` value.
   */
  epmp_state_t State() const {
    epmp_state_t state = {
        .mseccfg = static_cast<uint32_t>(mseccfg),
    };
    std::memcpy(&state.pmpcfg, &pmpcfg, sizeof(pmpcfg));
    std::memcpy(&state.pmpaddr, &pmpaddr, sizeof(pmpaddr));
    return state;
  }
};

/**
 * Map from PMP config register index to CSR_REG_PMPCFGN value.
 */
constexpr std::array<uint32_t, 4> kPmpcfgMap = {
    CSR_REG_PMPCFG0,
    CSR_REG_PMPCFG1,
    CSR_REG_PMPCFG2,
    CSR_REG_PMPCFG3,
};

/**
 * Map from PMP address register index to CSR_REG_PMPADDRN value.
 */
constexpr std::array<uint32_t, 16> kPmpaddrMap = {
    CSR_REG_PMPADDR0,  CSR_REG_PMPADDR1,  CSR_REG_PMPADDR2,  CSR_REG_PMPADDR3,
    CSR_REG_PMPADDR4,  CSR_REG_PMPADDR5,  CSR_REG_PMPADDR6,  CSR_REG_PMPADDR7,
    CSR_REG_PMPADDR8,  CSR_REG_PMPADDR9,  CSR_REG_PMPADDR10, CSR_REG_PMPADDR11,
    CSR_REG_PMPADDR12, CSR_REG_PMPADDR13, CSR_REG_PMPADDR14, CSR_REG_PMPADDR15,
};

/**
 * Helper function to call EXPECT_CSR_READ on all pmpcfg registers
 * returning the values provided.
 */
void ExpectPmpcfgRead(const PmpCsrs &expect) {
  auto packed = expect.PackCfg();
  for (size_t i = 0; i < packed.size(); ++i) {
    EXPECT_CSR_READ(kPmpcfgMap.at(i), packed.at(i));
  }
}

/**
 * Helper function to call EXPECT_CSR_READ on all pmpaddr registers
 * returning the values provided.
 */
void ExpectPmpaddrRead(const PmpCsrs &expect) {
  for (size_t i = 0; i < expect.pmpaddr.size(); ++i) {
    EXPECT_CSR_READ(kPmpaddrMap.at(i), expect.pmpaddr.at(i));
  }
}

/**
 * Helper function to call EXPECT_CSR_READ on the mseccfg register
 * returning the value provided.
 */
void ExpectMseccfgRead(const PmpCsrs &expect) {
  EXPECT_CSR_READ(CSR_REG_MSECCFG, static_cast<uint32_t>(expect.mseccfg));
  EXPECT_CSR_READ(CSR_REG_MSECCFGH,
                  static_cast<uint32_t>(expect.mseccfg >> 32));
}

/**
 * Helper function to call EXPECT_CSR_READ as necessary for an
 * internal `read_state` call with the expected values provided.
 */
void ExpectReadState(const PmpCsrs &expect) {
  ExpectPmpaddrRead(expect);
  ExpectPmpcfgRead(expect);
  ExpectMseccfgRead(expect);
}

TEST(EpmpCheckTest, Default) {
  mock_csr::MockCsr csr;

  ExpectReadState({});
  memset((void *)&epmp_state, 0, sizeof(epmp_state));
  EXPECT_EQ(epmp_state_check(), kErrorOk);
}

TEST(EpmpCheckTest, ErrorPmpaddr) {
  mock_csr::MockCsr csr;

  PmpCsrs bad;
  bad.pmpaddr[15] ^= 1 << 31;

  ExpectReadState(bad);
  memset((void *)&epmp_state, 0, sizeof(epmp_state));
  EXPECT_EQ(epmp_state_check(), kErrorEpmpBadCheck);
}

TEST(EpmpCheckTest, ErrorPmpcfg) {
  mock_csr::MockCsr csr;

  PmpCsrs bad;
  bad.pmpcfg[0] ^= 1;

  ExpectReadState(bad);
  memset((void *)&epmp_state, 0, sizeof(epmp_state));
  EXPECT_EQ(epmp_state_check(), kErrorEpmpBadCheck);
}

TEST(EpmpCheckTest, ErrorMseccfg) {
  mock_csr::MockCsr csr;

  PmpCsrs bad;
  bad.mseccfg ^= 1;

  ExpectReadState(bad);
  memset((void *)&epmp_state, 0, sizeof(epmp_state));
  EXPECT_EQ(epmp_state_check(), kErrorEpmpBadCheck);
}

TEST(EpmpTorTest, Entry0) {
  mock_csr::MockCsr csr;
  epmp_region_t region = {
      .start = 0,
      .end = 0,
  };

  // Configure registers for entry 0 (base address implicitly 0).
  PmpCsrs csrs;
  csrs.pmpcfg[0] = EPMP_CFG_L | EPMP_CFG_A_TOR | EPMP_CFG_R;
  csrs.pmpaddr[0] = region.end >> 2;
  memset((void *)&epmp_state, 0, sizeof(epmp_state));
  epmp_state_configure_tor(0, region, kEpmpPermLockedReadOnly);

  ExpectReadState(csrs);
  EXPECT_EQ(epmp_state_check(), kErrorOk);
}

TEST(EpmpTorTest, Entry1) {
  mock_csr::MockCsr csr;
  epmp_region_t region = {
      .start = 0x120,
      .end = 0x140,
  };

  // Configure registers for entry 1, with base address in entry 0.
  PmpCsrs csrs;
  csrs.pmpaddr[0] = region.start >> 2;
  csrs.pmpcfg[1] = EPMP_CFG_L | EPMP_CFG_A_TOR | EPMP_CFG_R;
  csrs.pmpaddr[1] = region.end >> 2;
  memset((void *)&epmp_state, 0, sizeof(epmp_state));
  epmp_state_configure_tor(1, region, kEpmpPermLockedReadOnly);

  ExpectReadState(csrs);
  EXPECT_EQ(epmp_state_check(), kErrorOk);
}

TEST(EpmpTorTest, Entry15) {
  mock_csr::MockCsr csr;
  epmp_region_t region = {
      .start = 0x120,
      .end = 0x140,
  };

  // Configure registers for entry 15, with base address in entry 14.
  PmpCsrs csrs;
  csrs.pmpaddr[14] = region.start >> 2;
  csrs.pmpcfg[15] = EPMP_CFG_L | EPMP_CFG_A_TOR | EPMP_CFG_R;
  csrs.pmpaddr[15] = region.end >> 2;

  memset((void *)&epmp_state, 0, sizeof(epmp_state));
  epmp_state_configure_tor(15, region, kEpmpPermLockedReadOnly);

  ExpectReadState(csrs);
  EXPECT_EQ(epmp_state_check(), kErrorOk);
}

TEST(EpmpTorTest, SharedAddress) {
  mock_csr::MockCsr csr;

  // Adjacent regions for entries.
  epmp_region_t region1 = {
      .start = 0x120,
      .end = 0x140,
  };
  epmp_region_t region2 = {
      .start = 0x140,
      .end = 0x180,
  };

  // Configure registers for entries 1 and 2, with base address in entry 0.
  PmpCsrs csrs;
  csrs.pmpaddr[0] = region1.start >> 2;
  csrs.pmpcfg[1] = EPMP_CFG_L | EPMP_CFG_A_TOR | EPMP_CFG_R | EPMP_CFG_X;
  csrs.pmpaddr[1] = region1.end >> 2;
  csrs.pmpcfg[2] = EPMP_CFG_L | EPMP_CFG_A_TOR | EPMP_CFG_R;
  csrs.pmpaddr[2] = region2.end >> 2;

  memset((void *)&epmp_state, 0, sizeof(epmp_state));
  epmp_state_configure_tor(1, region1, kEpmpPermLockedReadExecute);
  epmp_state_configure_tor(2, region2, kEpmpPermLockedReadOnly);

  ExpectReadState(csrs);
  EXPECT_EQ(epmp_state_check(), kErrorOk);
}

TEST(EpmpNa4Test, Entry0) {
  mock_csr::MockCsr csr;
  epmp_region_t region = {
      .start = 0xF4,
      .end = 0xF8,
  };

  // Configure registers for entry 0.
  PmpCsrs csrs;
  csrs.pmpcfg[0] = EPMP_CFG_L | EPMP_CFG_A_NA4 | EPMP_CFG_R | EPMP_CFG_X;
  csrs.pmpaddr[0] = region.start >> 2;

  memset((void *)&epmp_state, 0, sizeof(epmp_state));
  epmp_state_configure_na4(0, region, kEpmpPermLockedReadExecute);

  ExpectReadState(csrs);
  EXPECT_EQ(epmp_state_check(), kErrorOk);
}

TEST(EpmpNa4Test, Entry15) {
  mock_csr::MockCsr csr;
  epmp_region_t region = {
      .start = 0x0,
      .end = 0x4,
  };

  // Configure registers for entry 15.
  PmpCsrs csrs;
  csrs.pmpcfg[15] = EPMP_CFG_L | EPMP_CFG_A_NA4 | EPMP_CFG_R | EPMP_CFG_W;
  csrs.pmpaddr[15] = region.start >> 2;

  memset((void *)&epmp_state, 0, sizeof(epmp_state));
  epmp_state_configure_na4(15, region, kEpmpPermLockedReadWrite);

  ExpectReadState(csrs);
  EXPECT_EQ(epmp_state_check(), kErrorOk);
}

/**
 * Encode a region using the NAPOT address mode. This does not
 * do any validation of the values provided.
 *
 * Note: other address modes just require the address to be right
 * shifted by 2.
 */
uint32_t Napot(epmp_region_t region) {
  return (region.start >> 2) | ((region.end - region.start - 1) >> 3);
}

TEST(EpmpNapotTest, Entry0) {
  mock_csr::MockCsr csr;
  epmp_region_t region = {
      .start = 0xFF00,
      .end = 0xFF10,
  };

  // Configure registers for entry 0.
  PmpCsrs csrs;
  csrs.pmpcfg[0] = EPMP_CFG_L | EPMP_CFG_A_NAPOT | EPMP_CFG_R | EPMP_CFG_X;
  csrs.pmpaddr[0] = Napot(region);

  memset((void *)&epmp_state, 0, sizeof(epmp_state));
  epmp_state_configure_napot(0, region, kEpmpPermLockedReadExecute);

  ExpectReadState(csrs);
  EXPECT_EQ(epmp_state_check(), kErrorOk);
}

TEST(EpmpNapotTest, Entry15) {
  mock_csr::MockCsr csr;
  epmp_region_t region = {
      .start = 0x0,
      .end = 0x8,
  };

  // Configure registers for entry 15.
  PmpCsrs csrs;
  csrs.pmpcfg[15] = EPMP_CFG_L | EPMP_CFG_A_NAPOT | EPMP_CFG_R | EPMP_CFG_W;
  csrs.pmpaddr[15] = Napot(region);

  memset((void *)&epmp_state, 0, sizeof(epmp_state));
  epmp_state_configure_napot(15, region, kEpmpPermLockedReadWrite);

  ExpectReadState(csrs);
  EXPECT_EQ(epmp_state_check(), kErrorOk);
}

}  // namespace
}  // namespace epmp_unittest
