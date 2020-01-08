// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_MOCK_MMIO_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_MOCK_MMIO_H_

#include <stdint.h>

#include <memory>
#include <vector>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"

namespace mock_mmio {
/**
 * A MockDevice represents a mock implementation of an MMIO device.
 *
 * MockDevice provides two mockable member functions, representing a read and a
 * write at a particular offset from the base address. This class can be
 * converted into a |mmio_region_t| value, which, when used in |mmio.h|
 * functions like |read32()|, will map to the appropriate mock member function
 * calls.
 *
 * To maintain sequencing, |ReadN()| and |WriteN()| should not be
 * |EXPECT_CALL|'ed directly; instead, |EXPECT_READN| and |EXPECT_WRITEN| should
 * be used, instead.
 *
 * To use this class, |-DMOCK_MMIO| must be enabled in all translation units
 * using |mmio.h|.
 */
class MockDevice {
 public:
  MockDevice() = default;

  MockDevice(const MockDevice &) = delete;
  MockDevice &operator=(const MockDevice &) = delete;
  MockDevice(MockDevice &&) = delete;
  MockDevice &operator=(MockDevice &&) = delete;

  /**
   * Converts this MockDevice into a mmio_region_t opaque object,
   * which is compatible with |mmio.h| functions.
   */
  mmio_region_t region() { return {this}; }

  MOCK_METHOD(uint8_t, Read8, (ptrdiff_t offset));
  MOCK_METHOD(uint16_t, Read16, (ptrdiff_t offset));
  MOCK_METHOD(uint32_t, Read32, (ptrdiff_t offset));

  MOCK_METHOD(void, Write8, (ptrdiff_t offset, uint8_t value));
  MOCK_METHOD(void, Write16, (ptrdiff_t offset, uint16_t value));
  MOCK_METHOD(void, Write32, (ptrdiff_t offset, uint32_t value));
};

/**
 * Conveninence fixture for creating device tests.
 *
 * This class should be derived by a test fixture (along with |testing::Test|)
 * and used in a |TEST_F| block. Doing so will make the |EXPECT_READN| and
 * |EXPECT_WRITEN| conveinence macros useable.
 *
 * The device being mocked can be accessed in the test body with |this->dev()|.
 * |this->| is required in this case, since the name |dev| is not immediately
 * visible.
 */
class MmioTest {
 protected:
  MockDevice &dev() { return *dev_; }

 private:
  std::unique_ptr<MockDevice> dev_ = std::make_unique<MockDevice>();
  testing::InSequence seq_;
};

}  // namespace mock_mmio

/**
 * Expect a read to the device |dev| at the given offset, returning the given
 * 8-bit value.
 *
 * This expectation is sequenced with all other |EXPECT_READ| and |EXPECT_WRITE|
 * calls.
 */
#define EXPECT_READ8_AT(dev, offset, value) \
  EXPECT_CALL(dev, Read8(offset)).WillOnce(testing::Return(value))

/**
 * Expect a read to the device |dev| at the given offset, returning the given
 * 16-bit value.
 *
 * This expectation is sequenced with all other |EXPECT_READ| and |EXPECT_WRITE|
 * calls.
 */
#define EXPECT_READ16_AT(dev, offset, value) \
  EXPECT_CALL(dev, Read16(offset)).WillOnce(testing::Return(value))

/**
 * Expect a read to the device |dev| at the given offset, returning the given
 * 32-bit value.
 *
 * This expectation is sequenced with all other |EXPECT_READ| and |EXPECT_WRITE|
 * calls.
 */
#define EXPECT_READ32_AT(dev, offset, value) \
  EXPECT_CALL(dev, Read32(offset)).WillOnce(testing::Return(value))

/**
 * Expect a write to the device |dev| at the given offset with the given 8-bit
 * value.
 *
 * This expectation is sequenced with all other |EXPECT_READ| and |EXPECT_WRITE|
 * calls.
 */
#define EXPECT_WRITE8_AT(dev, offset, value) \
  EXPECT_CALL(dev, Write8(offset, value))

/**
 * Expect a write to the device |dev| at the given offset with the given 16-bit
 * value.
 *
 * This expectation is sequenced with all other |EXPECT_READ| and |EXPECT_WRITE|
 * calls.
 */
#define EXPECT_WRITE16_AT(dev, offset, value) \
  EXPECT_CALL(dev, Write16(offset, value))

/**
 * Expect a write to the device |dev| at the given offset with the given 32-bit
 * value.
 *
 * This expectation is sequenced with all other |EXPECT_READ| and |EXPECT_WRITE|
 * calls.
 */
#define EXPECT_WRITE32_AT(dev, offset, value) \
  EXPECT_CALL(dev, Write32(offset, value))

/**
 * Expect a read at the given offset, returning the given 8-bit value.
 *
 * This function is only available in tests using a fixture that derives
 * |DeviceTest|.
 *
 * This expectation is sequenced with all other |EXPECT_READ| and |EXPECT_WRITE|
 * calls.
 */
#define EXPECT_READ8(offset, value) EXPECT_READ8_AT(this->dev(), offset, value)

/**
 * Expect a read at the given offset, returning the given 16-bit value.
 *
 * This function is only available in tests using a fixture that derives
 * |DeviceTest|.
 *
 * This expectation is sequenced with all other |EXPECT_READ| and |EXPECT_WRITE|
 * calls.
 */
#define EXPECT_READ16(offset, value) \
  EXPECT_READ16_AT(this->dev(), offset, value)

/**
 * Expect a read at the given offset, returning the given 32-bit value.
 *
 * This function is only available in tests using a fixture that derives
 * |DeviceTest|.
 *
 * This expectation is sequenced with all other |EXPECT_READ| and |EXPECT_WRITE|
 * calls.
 */
#define EXPECT_READ32(offset, value) \
  EXPECT_READ32_AT(this->dev(), offset, value)

/**
 * Expect a write to the given offset with the given 8-bit value.
 *
 * This function is only available in tests using a fixture that derives
 * |DeviceTest|.
 *
 * This expectation is sequenced with all other |EXPECT_READ| and |EXPECT_WRITE|
 * calls.
 */
#define EXPECT_WRITE8(offset, value) \
  EXPECT_WRITE8_AT(this->dev(), offset, value);

/**
 * Expect a write to the given offset with the given 16-bit value.
 *
 * This function is only available in tests using a fixture that derives
 * |DeviceTest|.
 *
 * This expectation is sequenced with all other |EXPECT_READ| and |EXPECT_WRITE|
 * calls.
 */
#define EXPECT_WRITE16(offset, value) \
  EXPECT_WRITE16_AT(this->dev(), offset, value);

/**
 * Expect a write to the given offset with the given 32-bit value.
 *
 * This function is only available in tests using a fixture that derives
 * |DeviceTest|.
 *
 * This expectation is sequenced with all other |EXPECT_READ| and |EXPECT_WRITE|
 * calls.
 */
#define EXPECT_WRITE32(offset, value) \
  EXPECT_WRITE32_AT(this->dev(), offset, value);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_MOCK_MMIO_H_
