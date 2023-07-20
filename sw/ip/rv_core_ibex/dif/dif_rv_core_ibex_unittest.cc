// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rv_core_ibex.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

extern "C" {
#include "rv_core_ibex_regs.h"  // Generated.
}  // extern "C"

// We define global namespace == and << to make
// `dif_rv_core_ibex_addr_translation_mapping_t` work nicely with EXPECT_EQ.
bool operator==(const dif_rv_core_ibex_addr_translation_mapping_t a,
                const dif_rv_core_ibex_addr_translation_mapping_t b) {
  return !memcmp(&a, &b, sizeof(dif_rv_core_ibex_addr_translation_mapping_t));
}

std::ostream &operator<<(
    std::ostream &os,
    const dif_rv_core_ibex_addr_translation_mapping_t &mapping) {
  return os << "{\n"
            << "  .matching_addr = " << mapping.matching_addr << ",\n"
            << "  .remap_addr = " << mapping.remap_addr << ",\n"
            << "  .size = " << mapping.size << ",\n"
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

std::ostream &operator<<(std::ostream &os,
                         const dif_rv_core_ibex_crash_dump_info_t &info) {
  return os << "{\n"
            << "fault_state = {\n"
            << "  .mtval = " << info.fault_state.mtval << ",\n"
            << "  .mpec = " << info.fault_state.mpec << ",\n"
            << "  .mdaa = " << info.fault_state.mdaa << ",\n"
            << "  .mnpc = " << info.fault_state.mnpc << ",\n"
            << "  .mcpc = " << info.fault_state.mcpc << ",\n"
            << "},\n"
            << "previous_fault_state = {\n"
            << "  .mtval = " << info.previous_fault_state.mtval << ",\n"
            << "  .mpec = " << info.previous_fault_state.mpec << ",\n"
            << "},\n"
            << "double_fault = " << info.double_fault << ",\n"
            << "}";
}

bool operator==(const dif_rv_core_ibex_crash_dump_info_t a,
                const dif_rv_core_ibex_crash_dump_info_t b) {
  return memcmp(&a, &b, sizeof(dif_rv_core_ibex_crash_dump_info_t)) == 0;
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

class AddressTranslationTest
    : public RvCoreIbexTestInitialized,
      public testing::WithParamInterface<
          std::tuple<dif_rv_core_ibex_addr_translation_slot_t,
                     dif_rv_core_ibex_addr_translation_bus_t, uint32_t,
                     uint32_t, uint32_t, uint32_t>> {
 protected:
  static constexpr dif_rv_core_ibex_addr_translation_mapping_t kMapping = {
      .matching_addr = 0x9000000,
      .remap_addr = 0x2000000,
      .size = 0x8000,
  };

  uint32_t Napot(uint32_t addr, size_t size) { return addr | (size - 1) >> 1; }
};
constexpr dif_rv_core_ibex_addr_translation_mapping_t
    AddressTranslationTest::kMapping;

INSTANTIATE_TEST_SUITE_P(
    AddressTranslationTest, AddressTranslationTest,
    testing::ValuesIn(std::vector<
                      std::tuple<dif_rv_core_ibex_addr_translation_slot_t,
                                 dif_rv_core_ibex_addr_translation_bus_t,
                                 uint32_t, uint32_t, uint32_t, uint32_t>>{{
        {kDifRvCoreIbexAddrTranslationSlot_0, kDifRvCoreIbexAddrTranslationDBus,
         RV_CORE_IBEX_DBUS_ADDR_MATCHING_0_REG_OFFSET,
         RV_CORE_IBEX_DBUS_REMAP_ADDR_0_REG_OFFSET,
         RV_CORE_IBEX_DBUS_ADDR_EN_0_REG_OFFSET,
         RV_CORE_IBEX_DBUS_REGWEN_0_REG_OFFSET},

        {kDifRvCoreIbexAddrTranslationSlot_0, kDifRvCoreIbexAddrTranslationIBus,
         RV_CORE_IBEX_IBUS_ADDR_MATCHING_0_REG_OFFSET,
         RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_OFFSET,
         RV_CORE_IBEX_IBUS_ADDR_EN_0_REG_OFFSET,
         RV_CORE_IBEX_IBUS_REGWEN_0_REG_OFFSET},

        {kDifRvCoreIbexAddrTranslationSlot_1, kDifRvCoreIbexAddrTranslationDBus,
         RV_CORE_IBEX_DBUS_ADDR_MATCHING_1_REG_OFFSET,
         RV_CORE_IBEX_DBUS_REMAP_ADDR_1_REG_OFFSET,
         RV_CORE_IBEX_DBUS_ADDR_EN_1_REG_OFFSET,
         RV_CORE_IBEX_DBUS_REGWEN_1_REG_OFFSET},

        {kDifRvCoreIbexAddrTranslationSlot_1, kDifRvCoreIbexAddrTranslationIBus,
         RV_CORE_IBEX_IBUS_ADDR_MATCHING_1_REG_OFFSET,
         RV_CORE_IBEX_IBUS_REMAP_ADDR_1_REG_OFFSET,
         RV_CORE_IBEX_IBUS_ADDR_EN_1_REG_OFFSET,
         RV_CORE_IBEX_IBUS_REGWEN_1_REG_OFFSET},
    }}),
    [](const ::testing::TestParamInfo<AddressTranslationTest::ParamType>
           &info) {
      const auto slot = std::get<0>(info.param);
      const auto bus = std::get<1>(info.param);
      std::string name = "";
      name += bus == kDifRvCoreIbexAddrTranslationDBus ? "DBus" : "IBus";
      name += slot == kDifRvCoreIbexAddrTranslationSlot_0 ? "Slot0" : "Slot1";
      return name;
    });

TEST_P(AddressTranslationTest, DisableSuccess) {
  const auto slot = std::get<0>(GetParam());
  const auto bus = std::get<1>(GetParam());
  const auto en_reg = std::get<4>(GetParam());
  const auto r_regwen = std::get<5>(GetParam());

  EXPECT_READ32(r_regwen, 1);
  EXPECT_WRITE32(en_reg, 0);
  EXPECT_DIF_OK(dif_rv_core_ibex_disable_addr_translation(&ibex_, slot, bus));
}

TEST_P(AddressTranslationTest, EnableSuccess) {
  const auto slot = std::get<0>(GetParam());
  const auto bus = std::get<1>(GetParam());
  const auto en_reg = std::get<4>(GetParam());
  const auto r_regwen = std::get<5>(GetParam());

  EXPECT_READ32(r_regwen, 1);
  EXPECT_WRITE32(en_reg, 1);
  EXPECT_DIF_OK(dif_rv_core_ibex_enable_addr_translation(&ibex_, slot, bus));
}

TEST_P(AddressTranslationTest, ConfigureSuccess) {
  const auto slot = std::get<0>(GetParam());
  const auto bus = std::get<1>(GetParam());
  const auto r_matching = std::get<2>(GetParam());
  const auto r_remap = std::get<3>(GetParam());
  const auto r_regwen = std::get<5>(GetParam());

  EXPECT_READ32(r_regwen, 1);

  EXPECT_WRITE32(r_matching, 0x9003fff);
  EXPECT_WRITE32(r_remap, kMapping.remap_addr);

  EXPECT_DIF_OK(
      dif_rv_core_ibex_configure_addr_translation(&ibex_, slot, bus, kMapping));
}

TEST_P(AddressTranslationTest, PowerOfTwoAlignmentSuccess) {
  const auto slot = std::get<0>(GetParam());
  const auto bus = std::get<1>(GetParam());
  const auto r_matching = std::get<2>(GetParam());
  const auto r_remap = std::get<3>(GetParam());
  const auto r_regwen = std::get<5>(GetParam());

  dif_rv_core_ibex_addr_translation_mapping_t mapping = kMapping;
  mapping.matching_addr = 0x8000000;

  for (size_t i = 0; i < (sizeof(uint32_t) * 8) - 1; ++i) {
    mapping.size = 1u << i;

    EXPECT_READ32(r_regwen, 1);

    EXPECT_WRITE32(r_matching, Napot(mapping.matching_addr, mapping.size));
    EXPECT_WRITE32(r_remap, mapping.remap_addr);

    EXPECT_DIF_OK(dif_rv_core_ibex_configure_addr_translation(&ibex_, slot, bus,
                                                              mapping));
  }
}

TEST_P(AddressTranslationTest, NotPowerOfTwo) {
  const auto slot = std::get<0>(GetParam());
  const auto bus = std::get<1>(GetParam());

  dif_rv_core_ibex_addr_translation_mapping_t mapping = kMapping;
  mapping.size += 0x20;
  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_configure_addr_translation(&ibex_, slot, bus, mapping));
}

TEST_P(AddressTranslationTest, ReadSuccess) {
  const auto slot = std::get<0>(GetParam());
  const auto bus = std::get<1>(GetParam());
  const auto r_matching = std::get<2>(GetParam());
  const auto r_remap = std::get<3>(GetParam());

  EXPECT_READ32(r_matching, 0x9003fff);
  EXPECT_READ32(r_remap, kMapping.remap_addr);

  dif_rv_core_ibex_addr_translation_mapping_t mapping;
  EXPECT_DIF_OK(
      dif_rv_core_ibex_read_addr_translation(&ibex_, slot, bus, &mapping));

  EXPECT_EQ(mapping, kMapping);
}

TEST_P(AddressTranslationTest, LockSuccess) {
  const auto slot = std::get<0>(GetParam());
  const auto bus = std::get<1>(GetParam());
  const auto r_regwen = std::get<5>(GetParam());

  EXPECT_READ32(r_regwen, 1);
  EXPECT_WRITE32(r_regwen, 0);

  EXPECT_DIF_OK(dif_rv_core_ibex_lock_addr_translation(&ibex_, slot, bus));
}

TEST_P(AddressTranslationTest, Locked) {
  const auto slot = std::get<0>(GetParam());
  const auto bus = std::get<1>(GetParam());
  const auto r_regwen = std::get<5>(GetParam());

  EXPECT_READ32(r_regwen, 0);
  EXPECT_EQ(
      dif_rv_core_ibex_configure_addr_translation(&ibex_, slot, bus, kMapping),
      kDifLocked);

  EXPECT_READ32(r_regwen, 0);
  EXPECT_EQ(dif_rv_core_ibex_enable_addr_translation(&ibex_, slot, bus),
            kDifLocked);

  EXPECT_READ32(r_regwen, 0);
  EXPECT_EQ(dif_rv_core_ibex_disable_addr_translation(&ibex_, slot, bus),
            kDifLocked);

  // The lock function should quietly do nothing,
  // if address translation is already locked.
  EXPECT_READ32(r_regwen, 0);
  EXPECT_DIF_OK(dif_rv_core_ibex_lock_addr_translation(&ibex_, slot, bus));
}

TEST_F(AddressTranslationTest, BadArg) {
  const auto slot = kDifRvCoreIbexAddrTranslationSlot_0;
  const auto bus = kDifRvCoreIbexAddrTranslationDBus;
  const auto bad_slot = kDifRvCoreIbexAddrTranslationSlotCount;
  const auto bad_bus = kDifRvCoreIbexAddrTranslationBusCount;

  dif_rv_core_ibex_addr_translation_mapping_t mapping;
  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_configure_addr_translation(nullptr, slot, bus, mapping));
  EXPECT_DIF_BADARG(dif_rv_core_ibex_configure_addr_translation(
      &ibex_, slot, bad_bus, mapping));
  EXPECT_DIF_BADARG(dif_rv_core_ibex_configure_addr_translation(
      &ibex_, bad_slot, bus, mapping));

  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_read_addr_translation(nullptr, slot, bus, &mapping));
  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_read_addr_translation(&ibex_, bad_slot, bus, &mapping));
  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_read_addr_translation(&ibex_, slot, bad_bus, &mapping));
  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_read_addr_translation(&ibex_, slot, bus, nullptr));

  EXPECT_DIF_BADARG(dif_rv_core_ibex_lock_addr_translation(nullptr, slot, bus));
  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_lock_addr_translation(&ibex_, bad_slot, bus));
  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_lock_addr_translation(&ibex_, slot, bad_bus));

  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_enable_addr_translation(nullptr, slot, bus));
  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_enable_addr_translation(&ibex_, bad_slot, bus));
  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_enable_addr_translation(&ibex_, slot, bad_bus));

  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_disable_addr_translation(nullptr, slot, bus));
  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_disable_addr_translation(&ibex_, bad_slot, bus));
  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_disable_addr_translation(&ibex_, slot, bad_bus));
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

class FpgaInfoTest : public RvCoreIbexTestInitialized {};

TEST_F(FpgaInfoTest, ReadSuccess) {
  EXPECT_READ32(RV_CORE_IBEX_FPGA_INFO_REG_OFFSET, 0xf55ef65e);
  dif_rv_core_ibex_fpga_info_t info;
  EXPECT_DIF_OK(dif_rv_core_ibex_read_fpga_info(&ibex_, &info));
  EXPECT_EQ(info, 0xf55ef65e);
}

TEST_F(FpgaInfoTest, ReadZero) {
  EXPECT_READ32(RV_CORE_IBEX_FPGA_INFO_REG_OFFSET, 0);
  dif_rv_core_ibex_fpga_info_t info;
  EXPECT_DIF_OK(dif_rv_core_ibex_read_fpga_info(&ibex_, &info));
  EXPECT_EQ(info, 0);
}

TEST_F(FpgaInfoTest, ReadBadArg) {
  dif_rv_core_ibex_fpga_info_t info;
  EXPECT_DIF_BADARG(dif_rv_core_ibex_read_fpga_info(nullptr, &info));
  EXPECT_DIF_BADARG(dif_rv_core_ibex_read_fpga_info(&ibex_, nullptr));
}

class FatalErrorAlertTest : public RvCoreIbexTestInitialized {};

TEST_F(FatalErrorAlertTest, ReadAlertEnabled) {
  bool enabled;

  EXPECT_READ32(RV_CORE_IBEX_SW_FATAL_ERR_REG_OFFSET, 0x01);
  EXPECT_DIF_OK(dif_rv_core_ibex_get_sw_fatal_err_alert(&ibex_, &enabled));
  EXPECT_TRUE(enabled);

  EXPECT_READ32(RV_CORE_IBEX_SW_FATAL_ERR_REG_OFFSET, kMultiBitBool4True);
  EXPECT_DIF_OK(dif_rv_core_ibex_get_sw_fatal_err_alert(&ibex_, &enabled));
  EXPECT_TRUE(enabled);
}

TEST_F(FatalErrorAlertTest, ReadAlertDisabled) {
  bool enabled;

  EXPECT_READ32(RV_CORE_IBEX_SW_FATAL_ERR_REG_OFFSET, kMultiBitBool4False);
  EXPECT_DIF_OK(dif_rv_core_ibex_get_sw_fatal_err_alert(&ibex_, &enabled));
  EXPECT_FALSE(enabled);
}

TEST_F(FatalErrorAlertTest, TriggerSuccess) {
  EXPECT_WRITE32(RV_CORE_IBEX_SW_FATAL_ERR_REG_OFFSET, kMultiBitBool4True);
  EXPECT_DIF_OK(dif_rv_core_ibex_trigger_sw_fatal_err_alert(&ibex_));
}

TEST_F(FatalErrorAlertTest, ReadBadArg) {
  bool enabled;
  EXPECT_DIF_BADARG(dif_rv_core_ibex_get_sw_fatal_err_alert(nullptr, &enabled));
  EXPECT_DIF_BADARG(dif_rv_core_ibex_get_sw_fatal_err_alert(&ibex_, nullptr));
}

TEST_F(FatalErrorAlertTest, TriggerBadArg) {
  EXPECT_DIF_BADARG(dif_rv_core_ibex_trigger_sw_fatal_err_alert(nullptr));
}

class RecoverableErrorAlertTest : public RvCoreIbexTestInitialized {};

TEST_F(RecoverableErrorAlertTest, ReadAlertEnabled) {
  bool enabled;

  EXPECT_READ32(RV_CORE_IBEX_SW_RECOV_ERR_REG_OFFSET, 0x01);
  EXPECT_DIF_OK(dif_rv_core_ibex_get_sw_recov_err_alert(&ibex_, &enabled));
  EXPECT_TRUE(enabled);

  EXPECT_READ32(RV_CORE_IBEX_SW_RECOV_ERR_REG_OFFSET, kMultiBitBool4True);
  EXPECT_DIF_OK(dif_rv_core_ibex_get_sw_recov_err_alert(&ibex_, &enabled));
  EXPECT_TRUE(enabled);
}

TEST_F(RecoverableErrorAlertTest, ReadAlertDisabled) {
  bool enabled;

  EXPECT_READ32(RV_CORE_IBEX_SW_RECOV_ERR_REG_OFFSET, kMultiBitBool4False);
  EXPECT_DIF_OK(dif_rv_core_ibex_get_sw_recov_err_alert(&ibex_, &enabled));
  EXPECT_FALSE(enabled);
}

TEST_F(RecoverableErrorAlertTest, TriggerSuccess) {
  EXPECT_WRITE32(RV_CORE_IBEX_SW_RECOV_ERR_REG_OFFSET, kMultiBitBool4True);
  EXPECT_DIF_OK(dif_rv_core_ibex_trigger_sw_recov_err_alert(&ibex_));
}

TEST_F(RecoverableErrorAlertTest, ReadBadArg) {
  bool enabled;
  EXPECT_DIF_BADARG(dif_rv_core_ibex_get_sw_recov_err_alert(nullptr, &enabled));
  EXPECT_DIF_BADARG(dif_rv_core_ibex_get_sw_recov_err_alert(&ibex_, nullptr));
}

TEST_F(RecoverableErrorAlertTest, TriggerBadArg) {
  EXPECT_DIF_BADARG(dif_rv_core_ibex_trigger_sw_recov_err_alert(nullptr));
}

class ParseCrashDumpTest : public RvCoreIbexTestInitialized {};

TEST_F(ParseCrashDumpTest, DoubleFault) {
  dif_rv_core_ibex_crash_dump_info_t ref = {
      .fault_state = {.mtval = 0x55555555,
                      .mpec = 0x51555555,
                      .mdaa = 0x55515555,
                      .mnpc = 0x55555155,
                      .mcpc = 0x55555551},
      .previous_fault_state = {.mtval = 0x15555555, .mpec = 0x25555555},
      .double_fault = kDifToggleEnabled,
  };
  dif_rv_core_ibex_crash_dump_info_t dump = {0};

  uint32_t
      cpu_info[sizeof(dif_rv_core_ibex_crash_dump_info_t) / sizeof(uint32_t)];
  memcpy(cpu_info, &ref, sizeof(cpu_info));
  EXPECT_DIF_OK(
      dif_rv_core_ibex_parse_crash_dump(&ibex_, cpu_info, sizeof(ref), &dump));
  EXPECT_EQ(dump, ref);
}

TEST_F(ParseCrashDumpTest, SingleFault) {
  dif_rv_core_ibex_crash_dump_info_t ref = {
      .fault_state = {.mtval = 0x55555555,
                      .mpec = 0x51555555,
                      .mdaa = 0x55515555,
                      .mnpc = 0x55555155,
                      .mcpc = 0x55555551},
      .previous_fault_state = {.mtval = 0x15555555, .mpec = 0x25555555},
      .double_fault = kDifToggleDisabled,
  };
  dif_rv_core_ibex_crash_dump_info_t dump = {0};

  uint32_t
      cpu_info[sizeof(dif_rv_core_ibex_crash_dump_info_t) / sizeof(uint32_t)];
  memcpy(cpu_info, &ref, sizeof(cpu_info));
  EXPECT_DIF_OK(
      dif_rv_core_ibex_parse_crash_dump(&ibex_, cpu_info, sizeof(ref), &dump));
  EXPECT_EQ(dump, ref);
}

TEST_F(ParseCrashDumpTest, ReadBadArg) {
  dif_rv_core_ibex_crash_dump_info_t out;
  uint32_t info[9];
  EXPECT_DIF_BADARG(dif_rv_core_ibex_parse_crash_dump(nullptr, info, 9, &out));
  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_parse_crash_dump(&ibex_, nullptr, 9, &out));
  EXPECT_DIF_BADARG(dif_rv_core_ibex_parse_crash_dump(&ibex_, info, 7, &out));
  EXPECT_DIF_BADARG(
      dif_rv_core_ibex_parse_crash_dump(&ibex_, info, 9, nullptr));
}

}  // namespace dif_rv_core_ibex_test
