// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rv_core_ibex.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

extern "C" {
#include "rv_core_ibex_regs.h"  // Generated.
}  // extern "C"

// We define global namespace == and << to make `dif_i2c_timing_params_t` work
// nicely with EXPECT_EQ.
bool operator==(const dif_rv_core_ibex_addr_translation_region_t a,
                const dif_rv_core_ibex_addr_translation_region_t b) {
  return memcmp(&a, &b, sizeof(dif_rv_core_ibex_addr_translation_region_t)) ==
         0;
}

std::ostream &operator<<(
    std::ostream &os,
    const dif_rv_core_ibex_addr_translation_region_t &region) {
  return os << "{\n"
            << "ibus = {\n"
            << "  .matching_addr = " << region.ibus.matching_addr << ",\n"
            << "  .remap_addr = " << region.ibus.remap_addr << ",\n"
            << "  .size = " << region.ibus.size << ",\n"
            << "},\n"
            << "dbus = {\n"
            << "  .matching_addr = " << region.dbus.matching_addr << ",\n"
            << "  .remap_addr = " << region.dbus.remap_addr << ",\n"
            << "  .size = " << region.dbus.size << ",\n"
            << "},\n"
            << "}";
}

// We define global namespace == and << to make `dif_rv_core_ibex_nmi_state_t`
// work nicely with EXPECT_EQ.
bool operator==(const dif_rv_core_ibex_nmi_state_t a,
                const dif_rv_core_ibex_nmi_state_t b) {
  return memcmp(&a, &b, sizeof(dif_rv_core_ibex_nmi_state_t)) == 0;
}

std::ostream &operator<<(std::ostream &os,
                         const dif_rv_core_ibex_nmi_state_t &state) {
  return os << "{\n"
            << "state = {\n"
            << "  .alert_enabled = " << state.alert_enabled << ",\n"
            << "  .alert_raised = " << state.alert_raised << ",\n"
            << "  .wdog_enabled = " << state.wdog_enabled << ",\n"
            << "  .wdog_barked = " << state.wdog_barked << ",\n"
            << "}";
}

namespace dif_rv_core_ibex_test {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

// Base class for the rest fixtures in this file.
class RvCoreIbexTest : public testing::Test, public mock_mmio::MmioTest {};

// Base class for the rest of the tests in this file, provides a
// `dif_aes_t` instance.
class RvCoreIbexTestInitialized : public RvCoreIbexTest {
 protected:
  dif_rv_core_ibex_t ibex_;

  RvCoreIbexTestInitialized() {
    EXPECT_DIF_OK(dif_rv_core_ibex_init(dev().region(), &ibex_));
  }
};

class AddressTranslationTest : public RvCoreIbexTestInitialized {
 protected:
  static constexpr dif_rv_core_ibex_addr_translation_region_t kRegion = {
      .ibus =
          {
              .matching_addr = 0x9000000,
              .remap_addr = 0x2000000,
              .size = 0x8000,
          },
      .dbus =
          {
              .matching_addr = 0x9000000,
              .remap_addr = 0x2000000,
              .size = 0x8000,
          },
  };

  uint32_t Napot(uint32_t addr, size_t size) { return addr | (size - 1) >> 1; }
};
constexpr dif_rv_core_ibex_addr_translation_region_t
    AddressTranslationTest::kRegion;

TEST_F(AddressTranslationTest, Slot0Success) {
  EXPECT_READ32(RV_CORE_IBEX_DBUS_REGWEN_0_REG_OFFSET, 1);
  EXPECT_READ32(RV_CORE_IBEX_IBUS_REGWEN_0_REG_OFFSET, 1);

  EXPECT_WRITE32(RV_CORE_IBEX_IBUS_ADDR_MATCHING_0_REG_OFFSET, 0x9003fff);
  EXPECT_WRITE32(RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_OFFSET,
                 kRegion.ibus.remap_addr);
  EXPECT_WRITE32(RV_CORE_IBEX_IBUS_ADDR_EN_0_REG_OFFSET, 1);

  EXPECT_WRITE32(RV_CORE_IBEX_DBUS_ADDR_MATCHING_0_REG_OFFSET, 0x9003fff);
  EXPECT_WRITE32(RV_CORE_IBEX_DBUS_REMAP_ADDR_0_REG_OFFSET,
                 kRegion.dbus.remap_addr);
  EXPECT_WRITE32(RV_CORE_IBEX_DBUS_ADDR_EN_0_REG_OFFSET, 1);

  EXPECT_DIF_OK(dif_rv_core_ibex_configure_addr_translation(
      &ibex_, kDifRvCoreIbexAddrTranslationSlot_0, kRegion));
}

TEST_F(AddressTranslationTest, Slot1Success) {
  EXPECT_READ32(RV_CORE_IBEX_DBUS_REGWEN_1_REG_OFFSET, 1);
  EXPECT_READ32(RV_CORE_IBEX_IBUS_REGWEN_1_REG_OFFSET, 1);
  EXPECT_WRITE32(RV_CORE_IBEX_IBUS_ADDR_MATCHING_1_REG_OFFSET, 0x9003fff);
  EXPECT_WRITE32(RV_CORE_IBEX_IBUS_REMAP_ADDR_1_REG_OFFSET,
                 kRegion.ibus.remap_addr);
  EXPECT_WRITE32(RV_CORE_IBEX_IBUS_ADDR_EN_1_REG_OFFSET, 1);

  EXPECT_WRITE32(RV_CORE_IBEX_DBUS_ADDR_MATCHING_1_REG_OFFSET, 0x9003fff);
  EXPECT_WRITE32(RV_CORE_IBEX_DBUS_REMAP_ADDR_1_REG_OFFSET,
                 kRegion.dbus.remap_addr);
  EXPECT_WRITE32(RV_CORE_IBEX_DBUS_ADDR_EN_1_REG_OFFSET, 1);

  EXPECT_DIF_OK(dif_rv_core_ibex_configure_addr_translation(
      &ibex_, kDifRvCoreIbexAddrTranslationSlot_1, kRegion));
}

TEST_F(AddressTranslationTest, PowerOfTwoAlignmentSuccess) {
  dif_rv_core_ibex_addr_translation_region_t region = kRegion;

  region.ibus.matching_addr = 0x8000000;
  region.dbus.matching_addr = 0x8000000;

  for (size_t i = 0; i < (sizeof(uint32_t) * 8) - 1; ++i) {
    region.ibus.size = 1u << i;
    region.dbus.size = 1u << i;

    EXPECT_READ32(RV_CORE_IBEX_DBUS_REGWEN_0_REG_OFFSET, 1);
    EXPECT_READ32(RV_CORE_IBEX_IBUS_REGWEN_0_REG_OFFSET, 1);

    EXPECT_WRITE32(RV_CORE_IBEX_IBUS_ADDR_MATCHING_0_REG_OFFSET,
                   Napot(region.ibus.matching_addr, region.ibus.size));
    EXPECT_WRITE32(RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_OFFSET,
                   region.ibus.remap_addr);
    EXPECT_WRITE32(RV_CORE_IBEX_IBUS_ADDR_EN_0_REG_OFFSET, 1);

    EXPECT_WRITE32(RV_CORE_IBEX_DBUS_ADDR_MATCHING_0_REG_OFFSET,
                   Napot(region.dbus.matching_addr, region.dbus.size));
    EXPECT_WRITE32(RV_CORE_IBEX_DBUS_REMAP_ADDR_0_REG_OFFSET,
                   region.dbus.remap_addr);
    EXPECT_WRITE32(RV_CORE_IBEX_DBUS_ADDR_EN_0_REG_OFFSET, 1);

    EXPECT_DIF_OK(dif_rv_core_ibex_configure_addr_translation(
        &ibex_, kDifRvCoreIbexAddrTranslationSlot_0, region));
  }
}

TEST_F(AddressTranslationTest, ReadSlot0Success) {
  EXPECT_READ32(RV_CORE_IBEX_IBUS_ADDR_MATCHING_0_REG_OFFSET, 0x9003fff);
  EXPECT_READ32(RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_OFFSET,
                kRegion.ibus.remap_addr);

  EXPECT_READ32(RV_CORE_IBEX_DBUS_ADDR_MATCHING_0_REG_OFFSET, 0x9003fff);
  EXPECT_READ32(RV_CORE_IBEX_DBUS_REMAP_ADDR_0_REG_OFFSET,
                kRegion.dbus.remap_addr);

  dif_rv_core_ibex_addr_translation_region_t region;
  EXPECT_DIF_OK(dif_rv_core_ibex_read_addr_translation(
      &ibex_, kDifRvCoreIbexAddrTranslationSlot_0, &region));

  EXPECT_EQ(region, kRegion);
}

TEST_F(AddressTranslationTest, LockSlot0Success) {
  EXPECT_READ32(RV_CORE_IBEX_DBUS_REGWEN_0_REG_OFFSET, 1);
  EXPECT_WRITE32(RV_CORE_IBEX_DBUS_REGWEN_0_REG_OFFSET, 0);
  EXPECT_READ32(RV_CORE_IBEX_IBUS_REGWEN_0_REG_OFFSET, 1);
  EXPECT_WRITE32(RV_CORE_IBEX_IBUS_REGWEN_0_REG_OFFSET, 0);

  EXPECT_DIF_OK(dif_rv_core_ibex_lock_addr_translation(
      &ibex_, kDifRvCoreIbexAddrTranslationSlot_0));
}

TEST_F(AddressTranslationTest, LockSlot0LockedSuccess) {
  EXPECT_READ32(RV_CORE_IBEX_DBUS_REGWEN_0_REG_OFFSET, 0);
  EXPECT_READ32(RV_CORE_IBEX_IBUS_REGWEN_0_REG_OFFSET, 0);

  EXPECT_DIF_OK(dif_rv_core_ibex_lock_addr_translation(
      &ibex_, kDifRvCoreIbexAddrTranslationSlot_0));
}

TEST_F(AddressTranslationTest, LockSlot1Success) {
  EXPECT_READ32(RV_CORE_IBEX_DBUS_REGWEN_1_REG_OFFSET, 1);
  EXPECT_WRITE32(RV_CORE_IBEX_DBUS_REGWEN_1_REG_OFFSET, 0);
  EXPECT_READ32(RV_CORE_IBEX_IBUS_REGWEN_1_REG_OFFSET, 1);
  EXPECT_WRITE32(RV_CORE_IBEX_IBUS_REGWEN_1_REG_OFFSET, 0);

  EXPECT_DIF_OK(dif_rv_core_ibex_lock_addr_translation(
      &ibex_, kDifRvCoreIbexAddrTranslationSlot_1));
}

TEST_F(AddressTranslationTest, LockSlot1LockedSuccess) {
  EXPECT_READ32(RV_CORE_IBEX_DBUS_REGWEN_1_REG_OFFSET, 0);
  EXPECT_READ32(RV_CORE_IBEX_IBUS_REGWEN_1_REG_OFFSET, 0);

  EXPECT_DIF_OK(dif_rv_core_ibex_lock_addr_translation(
      &ibex_, kDifRvCoreIbexAddrTranslationSlot_1));
}

TEST_F(AddressTranslationTest, BadArg) {
  dif_rv_core_ibex_addr_translation_region_t region;
  EXPECT_DIF_BADARG(dif_rv_core_ibex_configure_addr_translation(
      nullptr, kDifRvCoreIbexAddrTranslationSlot_1, region));
  EXPECT_DIF_BADARG(dif_rv_core_ibex_configure_addr_translation(
      &ibex_, kDifRvCoreIbexAddrTranslationSlotCount, region));

  EXPECT_DIF_BADARG(dif_rv_core_ibex_read_addr_translation(
      nullptr, kDifRvCoreIbexAddrTranslationSlot_1, &region));
  EXPECT_DIF_BADARG(dif_rv_core_ibex_read_addr_translation(
      &ibex_, kDifRvCoreIbexAddrTranslationSlotCount, &region));
  EXPECT_DIF_BADARG(dif_rv_core_ibex_read_addr_translation(
      &ibex_, kDifRvCoreIbexAddrTranslationSlot_1, nullptr));

  EXPECT_DIF_BADARG(dif_rv_core_ibex_lock_addr_translation(
      nullptr, kDifRvCoreIbexAddrTranslationSlot_1));
  EXPECT_DIF_BADARG(dif_rv_core_ibex_lock_addr_translation(
      &ibex_, kDifRvCoreIbexAddrTranslationSlotCount));
}

TEST_F(AddressTranslationTest, Slot0DbusLocked) {
  EXPECT_READ32(RV_CORE_IBEX_DBUS_REGWEN_0_REG_OFFSET, 0);

  EXPECT_EQ(dif_rv_core_ibex_configure_addr_translation(
                &ibex_, kDifRvCoreIbexAddrTranslationSlot_0, kRegion),
            kDifLocked);
}

TEST_F(AddressTranslationTest, Slot0IbusLocked) {
  EXPECT_READ32(RV_CORE_IBEX_DBUS_REGWEN_0_REG_OFFSET, 1);
  EXPECT_READ32(RV_CORE_IBEX_IBUS_REGWEN_0_REG_OFFSET, 0);

  EXPECT_EQ(dif_rv_core_ibex_configure_addr_translation(
                &ibex_, kDifRvCoreIbexAddrTranslationSlot_0, kRegion),
            kDifLocked);
}

TEST_F(AddressTranslationTest, Slot1DbusLocked) {
  EXPECT_READ32(RV_CORE_IBEX_DBUS_REGWEN_1_REG_OFFSET, 0);

  EXPECT_EQ(dif_rv_core_ibex_configure_addr_translation(
                &ibex_, kDifRvCoreIbexAddrTranslationSlot_1, kRegion),
            kDifLocked);
}

TEST_F(AddressTranslationTest, Slot1IbusLocked) {
  EXPECT_READ32(RV_CORE_IBEX_DBUS_REGWEN_1_REG_OFFSET, 1);
  EXPECT_READ32(RV_CORE_IBEX_IBUS_REGWEN_1_REG_OFFSET, 0);

  EXPECT_EQ(dif_rv_core_ibex_configure_addr_translation(
                &ibex_, kDifRvCoreIbexAddrTranslationSlot_1, kRegion),
            kDifLocked);
}

TEST_F(AddressTranslationTest, NotPowerOfTwo) {
  dif_rv_core_ibex_addr_translation_region_t region = kRegion;
  region.dbus.size += 0x20;
  EXPECT_DIF_BADARG(dif_rv_core_ibex_configure_addr_translation(
      &ibex_, kDifRvCoreIbexAddrTranslationSlot_1, region));

  region.dbus.size -= 0x20;
  region.ibus.size += 0x20;
  EXPECT_DIF_BADARG(dif_rv_core_ibex_configure_addr_translation(
      &ibex_, kDifRvCoreIbexAddrTranslationSlot_0, region));
}

class ErrorStatusTest
    : public RvCoreIbexTestInitialized,
      public testing::WithParamInterface<
          std::tuple<uint32_t, dif_rv_core_ibex_error_status_t>> {};

TEST_P(ErrorStatusTest, ReadSuccess) {
  auto reg = std::get<0>(GetParam());
  auto status = std::get<1>(GetParam());

  EXPECT_READ32(RV_CORE_IBEX_ERR_STATUS_REG_OFFSET, {{reg, 1}});
  dif_rv_core_ibex_error_status_t error_status;
  EXPECT_DIF_OK(dif_rv_core_ibex_get_error_status(&ibex_, &error_status));
  EXPECT_EQ(status, error_status);
}

TEST_P(ErrorStatusTest, ClearSuccess) {
  auto reg = std::get<0>(GetParam());
  auto status = std::get<1>(GetParam());
  EXPECT_WRITE32(RV_CORE_IBEX_ERR_STATUS_REG_OFFSET, {{reg, 1}});
  EXPECT_DIF_OK(dif_rv_core_ibex_clear_error_status(&ibex_, status));
}

INSTANTIATE_TEST_SUITE_P(
    ErrorStatusTest, ErrorStatusTest,
    testing::ValuesIn(
        std::vector<std::tuple<uint32_t, dif_rv_core_ibex_error_status_t>>{{
            {RV_CORE_IBEX_ERR_STATUS_REG_INTG_ERR_BIT,
             kDifRvCoreIbexErrorStatusRegisterTransmissionIntegrity},
            {RV_CORE_IBEX_ERR_STATUS_FATAL_INTG_ERR_BIT,
             kDifRvCoreIbexErrorStatusFatalResponseIntegrity},
            {RV_CORE_IBEX_ERR_STATUS_FATAL_CORE_ERR_BIT,
             kDifRvCoreIbexErrorStatusFatalInternalError},
            {RV_CORE_IBEX_ERR_STATUS_RECOV_CORE_ERR_BIT,
             kDifRvCoreIbexErrorStatusRecoverableInternal},
        }}));

TEST_F(ErrorStatusTest, ReadBadArg) {
  dif_rv_core_ibex_error_status_t error_status;
  EXPECT_DIF_BADARG(dif_rv_core_ibex_get_error_status(nullptr, &error_status));
  EXPECT_DIF_BADARG(dif_rv_core_ibex_get_error_status(&ibex_, nullptr));
}

TEST_F(ErrorStatusTest, ClearBadArg) {
  EXPECT_DIF_BADARG(dif_rv_core_ibex_clear_error_status(
      nullptr, kDifRvCoreIbexErrorStatusRegisterTransmissionIntegrity));
  EXPECT_DIF_BADARG(dif_rv_core_ibex_clear_error_status(
      &ibex_, static_cast<dif_rv_core_ibex_error_status_t>(-1)));
}

class NMITest
    : public RvCoreIbexTestInitialized,
      public testing::WithParamInterface<dif_rv_core_ibex_nmi_state_t> {};

TEST_F(NMITest, EnableAlertSuccess) {
  EXPECT_WRITE32(RV_CORE_IBEX_NMI_ENABLE_REG_OFFSET,
                 {{RV_CORE_IBEX_NMI_ENABLE_ALERT_EN_BIT, 1}});
  EXPECT_DIF_OK(
      dif_rv_core_ibex_enable_nmi(&ibex_, kDifRvCoreIbexNmiSourceAlert));
}

TEST_F(NMITest, EnableWdogSuccess) {
  EXPECT_WRITE32(RV_CORE_IBEX_NMI_ENABLE_REG_OFFSET,
                 {{RV_CORE_IBEX_NMI_ENABLE_WDOG_EN_BIT, 1}});
  EXPECT_DIF_OK(
      dif_rv_core_ibex_enable_nmi(&ibex_, kDifRvCoreIbexNmiSourceWdog));
}

TEST_F(NMITest, EnableAllSuccess) {
  EXPECT_WRITE32(RV_CORE_IBEX_NMI_ENABLE_REG_OFFSET,
                 {{RV_CORE_IBEX_NMI_ENABLE_WDOG_EN_BIT, 1},
                  {RV_CORE_IBEX_NMI_ENABLE_ALERT_EN_BIT, 1}});
  EXPECT_DIF_OK(
      dif_rv_core_ibex_enable_nmi(&ibex_, kDifRvCoreIbexNmiSourceAll));
}

TEST_F(NMITest, EnableBadArg) {
  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_enable_nmi(nullptr, kDifRvCoreIbexNmiSourceWdog));
  EXPECT_DIF_BADARG(dif_rv_core_ibex_enable_nmi(
      &ibex_, static_cast<dif_rv_core_ibex_nmi_source_t>(-1)));
}

TEST_P(NMITest, GetStateSuccess) {
  dif_rv_core_ibex_nmi_state_t expected_state = GetParam();

  EXPECT_READ32(
      RV_CORE_IBEX_NMI_ENABLE_REG_OFFSET,
      {
          {RV_CORE_IBEX_NMI_ENABLE_ALERT_EN_BIT, expected_state.alert_enabled},
          {RV_CORE_IBEX_NMI_ENABLE_WDOG_EN_BIT, expected_state.wdog_enabled},
      });

  EXPECT_READ32(
      RV_CORE_IBEX_NMI_STATE_REG_OFFSET,
      {
          {RV_CORE_IBEX_NMI_STATE_ALERT_BIT, expected_state.alert_raised},
          {RV_CORE_IBEX_NMI_STATE_WDOG_BIT, expected_state.wdog_barked},
      });

  dif_rv_core_ibex_nmi_state_t state;
  EXPECT_DIF_OK(dif_rv_core_ibex_get_nmi_state(&ibex_, &state));
  EXPECT_EQ(expected_state, state);
}

INSTANTIATE_TEST_SUITE_P(
    NMITest, NMITest,
    testing::ValuesIn(std::vector<dif_rv_core_ibex_nmi_state_t>{{
        {true, false, false, false},
        {false, true, false, false},
        {false, false, true, false},
        {false, false, false, true},
    }}));

TEST_F(NMITest, GetStateBadArg) {
  dif_rv_core_ibex_nmi_state_t nmi_state;
  EXPECT_DIF_BADARG(dif_rv_core_ibex_get_nmi_state(nullptr, &nmi_state));
  EXPECT_DIF_BADARG(dif_rv_core_ibex_get_nmi_state(&ibex_, nullptr));
}

TEST_F(NMITest, ClearAlertSuccess) {
  EXPECT_WRITE32(RV_CORE_IBEX_NMI_STATE_REG_OFFSET,
                 {{RV_CORE_IBEX_NMI_STATE_ALERT_BIT, 1}});
  EXPECT_DIF_OK(
      dif_rv_core_ibex_clear_nmi_state(&ibex_, kDifRvCoreIbexNmiSourceAlert));
}

TEST_F(NMITest, ClearWdogSuccess) {
  EXPECT_WRITE32(RV_CORE_IBEX_NMI_STATE_REG_OFFSET,
                 {{RV_CORE_IBEX_NMI_STATE_WDOG_BIT, 1}});
  EXPECT_DIF_OK(
      dif_rv_core_ibex_clear_nmi_state(&ibex_, kDifRvCoreIbexNmiSourceWdog));
}

TEST_F(NMITest, ClearAllSuccess) {
  EXPECT_WRITE32(RV_CORE_IBEX_NMI_STATE_REG_OFFSET,
                 {{RV_CORE_IBEX_NMI_STATE_WDOG_BIT, 1},
                  {RV_CORE_IBEX_NMI_ENABLE_ALERT_EN_BIT, 1}});
  EXPECT_DIF_OK(
      dif_rv_core_ibex_clear_nmi_state(&ibex_, kDifRvCoreIbexNmiSourceAll));
}

TEST_F(NMITest, ClearBadArg) {
  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_clear_nmi_state(nullptr, kDifRvCoreIbexNmiSourceWdog));
  EXPECT_DIF_BADARG(dif_rv_core_ibex_clear_nmi_state(
      &ibex_, static_cast<dif_rv_core_ibex_nmi_source_t>(-1)));
}

class RndTest : public RvCoreIbexTestInitialized {};

TEST_F(RndTest, ReadSuccess) {
  EXPECT_READ32(RV_CORE_IBEX_RND_STATUS_REG_OFFSET,
                {{RV_CORE_IBEX_RND_STATUS_RND_DATA_VALID_BIT, true}});
  EXPECT_READ32(RV_CORE_IBEX_RND_DATA_REG_OFFSET, 0xf55ef65e);

  uint32_t data;
  EXPECT_DIF_OK(dif_rv_core_ibex_read_rnd_data(&ibex_, &data));
  EXPECT_EQ(data, 0xf55ef65e);
}

TEST_F(RndTest, ReadBadArg) {
  uint32_t data;
  EXPECT_DIF_BADARG(dif_rv_core_ibex_read_rnd_data(nullptr, &data));
  EXPECT_DIF_BADARG(dif_rv_core_ibex_read_rnd_data(&ibex_, nullptr));
}

TEST_F(RndTest, ReadNotValid) {
  EXPECT_READ32(RV_CORE_IBEX_RND_STATUS_REG_OFFSET,
                {{RV_CORE_IBEX_RND_STATUS_RND_DATA_VALID_BIT, false}});
  uint32_t data;
  EXPECT_EQ(dif_rv_core_ibex_read_rnd_data(&ibex_, &data), kDifError);
}

TEST_F(RndTest, StatusValid) {
  EXPECT_READ32(RV_CORE_IBEX_RND_STATUS_REG_OFFSET,
                {{RV_CORE_IBEX_RND_STATUS_RND_DATA_VALID_BIT, true}});

  dif_rv_core_ibex_rnd_status_t status;
  EXPECT_DIF_OK(dif_rv_core_ibex_get_rnd_status(&ibex_, &status));
  EXPECT_EQ(status, kDifRvCoreIbexRndStatusValid);
}

TEST_F(RndTest, StatusFipsCompliant) {
  EXPECT_READ32(RV_CORE_IBEX_RND_STATUS_REG_OFFSET,
                {{RV_CORE_IBEX_RND_STATUS_RND_DATA_FIPS_BIT, true}});

  dif_rv_core_ibex_rnd_status_t status;
  EXPECT_DIF_OK(dif_rv_core_ibex_get_rnd_status(&ibex_, &status));
  EXPECT_EQ(status, kDifRvCoreIbexRndStatusFipsCompliant);
}

TEST_F(RndTest, StatusBadArg) {
  dif_rv_core_ibex_rnd_status_t status;
  EXPECT_DIF_BADARG(dif_rv_core_ibex_get_rnd_status(nullptr, &status));
  EXPECT_DIF_BADARG(dif_rv_core_ibex_get_rnd_status(&ibex_, nullptr));
}
}  // namespace dif_rv_core_ibex_test
