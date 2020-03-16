// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/mock_mmio.h"

extern "C" {
#include "sw/device/lib/dif/dif_pinmux.h"
#include "pinmux_regs.h"  // Generated.
}

namespace dif_pinmux_test {
namespace {
using testing::Test;
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;

class PinmuxTest : public Test, public MmioTest {
 protected:
  mmio_region_t base_addr_ = dev().region();
  dif_pinmux_t dif_pinmux_ = {
      /* base_addr = */ base_addr_,
  };
};

class InitTest : public PinmuxTest {
 protected:
  InitTest() {
    EXPECT_EQ(insel_registers_.size(), PINMUX_PERIPH_INSEL_MULTIREG_COUNT);
    EXPECT_EQ(outsel_registers_.size(), PINMUX_MIO_OUTSEL_MULTIREG_COUNT);
  }

  void ExpectInitReset() {
    EXPECT_READ32(PINMUX_REGEN_REG_OFFSET, 1);

    for (const auto &reg : insel_registers_) {
      EXPECT_WRITE32(reg, 0);
    }

    for (const auto &reg : outsel_registers_) {
      EXPECT_WRITE32(reg, 0x2082082);
    }
  }

  std::vector<ptrdiff_t> insel_registers_{
      PINMUX_PERIPH_INSEL0_REG_OFFSET, PINMUX_PERIPH_INSEL1_REG_OFFSET,
      PINMUX_PERIPH_INSEL2_REG_OFFSET, PINMUX_PERIPH_INSEL3_REG_OFFSET,
      PINMUX_PERIPH_INSEL4_REG_OFFSET, PINMUX_PERIPH_INSEL5_REG_OFFSET,
      PINMUX_PERIPH_INSEL6_REG_OFFSET,
  };

  std::vector<ptrdiff_t> outsel_registers_{
      PINMUX_MIO_OUTSEL0_REG_OFFSET, PINMUX_MIO_OUTSEL1_REG_OFFSET,
      PINMUX_MIO_OUTSEL2_REG_OFFSET, PINMUX_MIO_OUTSEL3_REG_OFFSET,
      PINMUX_MIO_OUTSEL4_REG_OFFSET, PINMUX_MIO_OUTSEL5_REG_OFFSET,
      PINMUX_MIO_OUTSEL6_REG_OFFSET,
  };
};

TEST_F(InitTest, NullArgs) {
  EXPECT_EQ(dif_pinmux_init(base_addr_, nullptr), kDifPinmuxBadArg);
}

TEST_F(InitTest, RegistersLocked) {
  EXPECT_READ32(PINMUX_REGEN_REG_OFFSET, 0);

  EXPECT_EQ(dif_pinmux_init(base_addr_, &dif_pinmux_), kDifPinmuxInitLocked);
}

TEST_F(InitTest, Success) {
  ExpectInitReset();

  EXPECT_EQ(dif_pinmux_init(base_addr_, &dif_pinmux_), kDifPinmuxInitOk);
}

class RegistersLockTest : public PinmuxTest {};

TEST_F(RegistersLockTest, NullArgs) {
  EXPECT_EQ(dif_pinmux_registers_lock(nullptr), kDifPinmuxBadArg);
}

TEST_F(RegistersLockTest, Success) {
  EXPECT_WRITE32(PINMUX_REGEN_REG_OFFSET, 0);

  EXPECT_EQ(dif_pinmux_registers_lock(&dif_pinmux_), kDifPinmuxOk);
}

class SetTests : public PinmuxTest {
 protected:
  // Tests should not rely on DIF defined constants and defines for setting
  // expectations.
  static constexpr uint32_t kExpectConstantZero = 0;

  static constexpr uint32_t kExpectInselFirstIn = 2;
  static constexpr uint32_t kExpectInselLastIn =
      kExpectInselFirstIn + (PINMUX_PARAM_NMIOPADS - 1);

  static constexpr uint32_t kExpectOutselFirstOut = 3;
  static constexpr uint32_t kExpectOutselLastOut =
      kExpectOutselFirstOut + (PINMUX_PARAM_NMIOPERIPHOUT - 1);

  struct Register {
    ptrdiff_t offset;    // Register offset from the base.
    uint8_t last_field;  // Last field offset in the register.
  };

  // Set multireg expectations, one field per call for every multireg register.
  void ExpectSetTests(const std::vector<Register> &regs, uint32_t field_width,
                      uint32_t field_mask, uint32_t value) {
    for (const auto &reg : regs) {
      for (uint32_t i = 0; i <= reg.last_field; i += field_width) {
        EXPECT_MASK32(reg.offset, {{i, field_mask, value}});
      }
    }
  }
};

class InselSet : public SetTests {
 protected:
  InselSet() {
    EXPECT_EQ(registers_.size(), PINMUX_PERIPH_INSEL_MULTIREG_COUNT);
  }

  std::vector<Register> registers_ = {
      {
          PINMUX_PERIPH_INSEL0_REG_OFFSET, PINMUX_PERIPH_INSEL0_IN4_OFFSET,
      },
      {
          PINMUX_PERIPH_INSEL1_REG_OFFSET, PINMUX_PERIPH_INSEL1_IN9_OFFSET,
      },
      {
          PINMUX_PERIPH_INSEL2_REG_OFFSET, PINMUX_PERIPH_INSEL2_IN14_OFFSET,
      },
      {
          PINMUX_PERIPH_INSEL3_REG_OFFSET, PINMUX_PERIPH_INSEL3_IN19_OFFSET,
      },
      {
          PINMUX_PERIPH_INSEL4_REG_OFFSET, PINMUX_PERIPH_INSEL4_IN24_OFFSET,
      },
      {
          PINMUX_PERIPH_INSEL5_REG_OFFSET, PINMUX_PERIPH_INSEL5_IN29_OFFSET,
      },
      {
          PINMUX_PERIPH_INSEL6_REG_OFFSET, PINMUX_PERIPH_INSEL6_IN31_OFFSET,
      },
  };
};

TEST_F(InselSet, NullArgs) {
  EXPECT_EQ(dif_pinmux_insel_set(nullptr, 0, 0), kDifPinmuxBadArg);
}

TEST_F(InselSet, BadArgs) {
  EXPECT_EQ(dif_pinmux_insel_set(&dif_pinmux_, 0, kDifPinmuxInselLast + 1),
            kDifPinmuxBadArg);

  EXPECT_EQ(
      dif_pinmux_insel_set(&dif_pinmux_, kDifPinmuxPeripheralInLast + 1, 0),
      kDifPinmuxBadArg);
}

TEST_F(InselSet, Success) {
  // Set first MIO select variant for every multireg register.
  ExpectSetTests(registers_, PINMUX_PERIPH_INSEL_IN_FIELD_WIDTH,
                 PINMUX_PERIPH_INSEL0_IN0_MASK, kExpectConstantZero);

  for (dif_pinmux_peripheral_in_t i = 0; i <= kDifPinmuxPeripheralInLast; ++i) {
    EXPECT_EQ(dif_pinmux_insel_set(&dif_pinmux_, i, 0), kDifPinmuxOk);
  }

  // Set the last MIO select variant for every multireg register.
  ExpectSetTests(registers_, PINMUX_PERIPH_INSEL_IN_FIELD_WIDTH,
                 PINMUX_PERIPH_INSEL0_IN0_MASK, kDifPinmuxInselLast);

  for (dif_pinmux_peripheral_in_t i = 0; i <= kDifPinmuxPeripheralInLast; ++i) {
    EXPECT_EQ(dif_pinmux_insel_set(&dif_pinmux_, i, kExpectInselLastIn),
              kDifPinmuxOk);
  }
}

class OutselSet : public SetTests {
 protected:
  OutselSet() {
    EXPECT_EQ(registers_.size(), PINMUX_MIO_OUTSEL_MULTIREG_COUNT);
  }

  std::vector<Register> registers_ = {
      {
          PINMUX_MIO_OUTSEL0_REG_OFFSET, PINMUX_MIO_OUTSEL0_OUT4_OFFSET,
      },
      {
          PINMUX_MIO_OUTSEL1_REG_OFFSET, PINMUX_MIO_OUTSEL1_OUT9_OFFSET,
      },
      {
          PINMUX_MIO_OUTSEL2_REG_OFFSET, PINMUX_MIO_OUTSEL2_OUT14_OFFSET,
      },
      {
          PINMUX_MIO_OUTSEL3_REG_OFFSET, PINMUX_MIO_OUTSEL3_OUT19_OFFSET,
      },
      {
          PINMUX_MIO_OUTSEL4_REG_OFFSET, PINMUX_MIO_OUTSEL4_OUT24_OFFSET,
      },
      {
          PINMUX_MIO_OUTSEL5_REG_OFFSET, PINMUX_MIO_OUTSEL5_OUT29_OFFSET,
      },
      {
          PINMUX_MIO_OUTSEL6_REG_OFFSET, PINMUX_MIO_OUTSEL6_OUT31_OFFSET,
      },
  };
};

TEST_F(OutselSet, NullArgs) {
  EXPECT_EQ(dif_pinmux_outsel_set(nullptr, 0, 0), kDifPinmuxBadArg);
}

TEST_F(OutselSet, BadArgs) {
  EXPECT_EQ(dif_pinmux_outsel_set(&dif_pinmux_, kDifPinmuxMioOutLast + 1, 0),
            kDifPinmuxBadArg);

  EXPECT_EQ(dif_pinmux_outsel_set(&dif_pinmux_, 0, kDifPinmuxOutselLast + 1),
            kDifPinmuxBadArg);
}

TEST_F(OutselSet, Success) {
  // Set first peripheral select variant for every multireg register.
  ExpectSetTests(registers_, PINMUX_MIO_OUTSEL_OUT_FIELD_WIDTH,
                 PINMUX_MIO_OUTSEL0_OUT0_MASK, kExpectConstantZero);

  for (dif_pinmux_mio_out_t i = 0; i <= kDifPinmuxMioOutLast; ++i) {
    EXPECT_EQ(dif_pinmux_outsel_set(&dif_pinmux_, i, 0), kDifPinmuxOk);
  }

  // Set the last peripehral select variant for every multireg register.
  ExpectSetTests(registers_, PINMUX_MIO_OUTSEL_OUT_FIELD_WIDTH,
                 PINMUX_MIO_OUTSEL0_OUT0_MASK, kExpectOutselLastOut);

  for (dif_pinmux_mio_out_t i = 0; i <= kDifPinmuxMioOutLast; ++i) {
    EXPECT_EQ(dif_pinmux_outsel_set(&dif_pinmux_, i, kDifPinmuxOutselLast),
              kDifPinmuxOk);
  }
}

}  // namespace
}  // namespace dif_pinmux_test
