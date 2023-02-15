// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/ip/aes/model/aes_modes.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_adc_ctrl.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_csrng_shared.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_pattgen.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwm.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/hmac_testutils.h"
#include "sw/device/lib/testing/i2c_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_macros.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "adc_ctrl_regs.h"     // Generated.
#include "aes_regs.h"          // Generated.
#include "entropy_src_regs.h"  // Generated.
#include "hmac_regs.h"         // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "i2c_regs.h"       // Generated.
#include "kmac_regs.h"      // Generated.
#include "pattgen_regs.h"   // Generated.
#include "pwm_regs.h"       // Generated.
#include "spi_host_regs.h"  // Generated.
#include "uart_regs.h"      // Generated.

OTTF_DEFINE_TEST_CONFIG(.enable_concurrency = true,
                        .enable_uart_flow_control = true,
                        .can_clobber_uart = false, );

/**
 * Peripheral DIF Handles.
 */
static dif_pinmux_t pinmux;
static dif_gpio_t gpio;
static dif_adc_ctrl_t adc_ctrl;
static dif_entropy_src_t entropy_src;
static dif_csrng_t csrng;
static dif_edn_t edn_0;
static dif_edn_t edn_1;
static dif_aes_t aes;
static dif_hmac_t hmac;
static dif_kmac_t kmac;
static dif_i2c_t i2c_0;
static dif_i2c_t i2c_1;
static dif_i2c_t i2c_2;
static dif_spi_device_handle_t spi_device;
static dif_spi_host_t spi_host_0;
static dif_spi_host_t spi_host_1;
static dif_uart_t uart_1;
static dif_uart_t uart_2;
static dif_uart_t uart_3;
static dif_pattgen_t pattgen;
static dif_pwm_t pwm;
static dif_flash_ctrl_state_t flash_ctrl;

static const dif_i2c_t *i2c_handles[] = {&i2c_0, &i2c_1, &i2c_2};
static const dif_uart_t *uart_handles[] = {&uart_1, &uart_2, &uart_3};
static dif_kmac_operation_state_t kmac_operation_state;
static const dif_pattgen_channel_t pattgen_channels[] = {kDifPattgenChannel0,
                                                         kDifPattgenChannel1};
static const dif_pwm_channel_t pwm_channels[PWM_PARAM_N_OUTPUTS] = {
    kDifPwmChannel0, kDifPwmChannel1, kDifPwmChannel2,
    kDifPwmChannel3, kDifPwmChannel4, kDifPwmChannel5,
};

/**
 * Test configuration parameters.
 */
enum {
  /**
   * Test timeout parameter.
   */
  kTestTimeoutMicros = 1000,  // 1ms
  /**
   * ADC controller parameters.
   */
  kAdcCtrlPowerUpTimeAonCycles = 15,  // maximum power-up time
  /**
   * EDN parameters.
   */
  kEdn0ReseedInterval = 32,
  kEdn1ReseedInterval = 4,
  /**
   * KMAC parameters.
   */
  kKmacEntropyReseedInterval = 1,
  kKmacEntropyHashThreshold = 1,  // KMAC operations between entropy requests
  kKmacEntropyWaitTimer = 0xffff,
  kKmacEntropyPrescaler = 0x3ff,
  kKmacMessageLength = 200,
  kKmacDigestLength = 16,
  /**
   * I2C parameters.
   */
  kI2cSdaRiseFallTimeNs = 10,
  kI2cDeviceMask = 0x7f,
  kI2c0DeviceAddress0 = 0x11,
  kI2c0DeviceAddress1 = 0x22,
  kI2c1DeviceAddress0 = 0x33,
  kI2c1DeviceAddress1 = 0x44,
  kI2c2DeviceAddress0 = 0x55,
  kI2c2DeviceAddress1 = 0x66,
  kI2c0TargetAddress = 0x01,
  kI2c1TargetAddress = 0x02,
  kI2c2TargetAddress = 0x03,
  /**
   * UART parameters.
   */
  kUartFifoDepth = 32,
  /**
   * Pattern Generator parameters.
   */
  kPattgenClockDivisor = 0,
  kPattgenSeedPatternLowerWord = 0xaaaaaaaa,
  kPattgenSeedPatternUpperWord = 0xaaaaaaaa,
  kPattgenSeedPatternLength = 64,
  kPattgenNumPatternRepetitions = 1024,
  /**
   * PWM parameters.
   */
  kPwmClockDivisor = 1,
  kPwmBeatsPerCycle = 2,
  kPwmOnBeats = 1,
  kPwmPhaseDelayBeats = 0,
  /**
   * SPI Host parameters.
   */
  kSpiHost1Csid = 0xaabbaabb,
  kSpiHost1TxDataWord = 0xaaaaaaaa,
};

/**
 * These symbols are meant to be backdoor read by the testbench. Due to current
 * DV infrastructure limitations, these must be `volatile const` to be accessed
 * by the testbench.
 */
static volatile const uint32_t kI2cSclPeriodNs = 1000;
static volatile uint32_t peripheral_clock_period_ns;

/**
 * Pinmux pad configurations.
 */
static const pinmux_pad_attributes_t pinmux_pad_attributes[] = {
    // Enable pull-ups for spi_host_0 data pins to avoid floating inputs.
    {
        .pad = kTopEarlgreyDirectPadsSpiHost0Sd0,
        .kind = kDifPinmuxPadKindDio,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
    {
        .pad = kTopEarlgreyDirectPadsSpiHost0Sd1,
        .kind = kDifPinmuxPadKindDio,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
    {
        .pad = kTopEarlgreyDirectPadsSpiHost0Sd2,
        .kind = kDifPinmuxPadKindDio,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
    {
        .pad = kTopEarlgreyDirectPadsSpiHost0Sd3,
        .kind = kDifPinmuxPadKindDio,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
    // Enable pull-ups for spi_host_1 data pins to avoid floating inputs.
    {
        .pad = kTopEarlgreyMuxedPadsIoa2,  // SD0
        .kind = kDifPinmuxPadKindMio,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
    {
        .pad = kTopEarlgreyMuxedPadsIor11,  // SD1
        .kind = kDifPinmuxPadKindMio,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
    {
        .pad = kTopEarlgreyMuxedPadsIor12,  // SD2
        .kind = kDifPinmuxPadKindMio,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
    {
        .pad = kTopEarlgreyMuxedPadsIor13,  // SD3
        .kind = kDifPinmuxPadKindMio,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
};

/**
 * The mask share, used to mask kAesKey.
 */
static const uint8_t kAesKeyShare1[] = {
    0x0f, 0x1f, 0x2f, 0x3f, 0x4f, 0x5f, 0x6f, 0x7f, 0x8f, 0x9f, 0xaf,
    0xbf, 0xcf, 0xdf, 0xef, 0xff, 0x0a, 0x1a, 0x2a, 0x3a, 0x4a, 0x5a,
    0x6a, 0x7a, 0x8a, 0x9a, 0xaa, 0xba, 0xca, 0xda, 0xea, 0xfa,
};

static const uint8_t kHmacKey[] = {
    0x0f, 0x1f, 0x2f, 0x3f, 0x4f, 0x5f, 0x6f, 0x7f,
};

static const dif_kmac_key_t kKmacKey = {
    .share0 = {0x43424140, 0x47464544, 0x4b4a4948, 0x4f4e4f4c, 0x53525150,
               0x57565554, 0x5b5a5958, 0x5f5e5d5c},
    .share1 = {0},
    .length = kDifKmacKeyLen256,
};

static const char *kKmacMessage =
    "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f"
    "\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f"
    "\x20\x21\x22\x23\x24\x25\x26\x27\x28\x29\x2a\x2b\x2c\x2d\x2e\x2f"
    "\x30\x31\x32\x33\x34\x35\x36\x37\x38\x39\x3a\x3b\x3c\x3d\x3e\x3f"
    "\x40\x41\x42\x43\x44\x45\x46\x47\x48\x49\x4a\x4b\x4c\x4d\x4e\x4f"
    "\x50\x51\x52\x53\x54\x55\x56\x57\x58\x59\x5a\x5b\x5c\x5d\x5e\x5f"
    "\x60\x61\x62\x63\x64\x65\x66\x67\x68\x69\x6a\x6b\x6c\x6d\x6e\x6f"
    "\x70\x71\x72\x73\x74\x75\x76\x77\x78\x79\x7a\x7b\x7c\x7d\x7e\x7f"
    "\x80\x81\x82\x83\x84\x85\x86\x87\x88\x89\x8a\x8b\x8c\x8d\x8e\x8f"
    "\x90\x91\x92\x93\x94\x95\x96\x97\x98\x99\x9a\x9b\x9c\x9d\x9e\x9f"
    "\xa0\xa1\xa2\xa3\xa4\xa5\xa6\xa7\xa8\xa9\xaa\xab\xac\xad\xae\xaf"
    "\xb0\xb1\xb2\xb3\xb4\xb5\xb6\xb7\xb8\xb9\xba\xbb\xbc\xbd\xbe\xbf"
    "\xc0\xc1\xc2\xc3\xc4\xc5\xc6\xc7";

static const uint8_t kUartMessage[] = {
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
};

static const uint8_t kI2cMessage[] = {
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
};

/**
 * Initializes all DIF handles for each peripheral used in this test.
 */
static void init_peripheral_handles(void) {
  CHECK_DIF_OK(dif_adc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_ADC_CTRL_AON_BASE_ADDR), &adc_ctrl));
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  CHECK_DIF_OK(dif_csrng_init(
      mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR), &csrng));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR), &edn_0));
  CHECK_DIF_OK(
      dif_edn_init(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR), &edn_1));
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));
  CHECK_DIF_OK(
      dif_hmac_init(mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR), &hmac));
  CHECK_DIF_OK(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  // UART 0 is already configured (and used) by the OTTF.
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART1_BASE_ADDR), &uart_1));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART2_BASE_ADDR), &uart_2));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART3_BASE_ADDR), &uart_3));
  CHECK_DIF_OK(
      dif_i2c_init(mmio_region_from_addr(TOP_EARLGREY_I2C0_BASE_ADDR), &i2c_0));
  CHECK_DIF_OK(
      dif_i2c_init(mmio_region_from_addr(TOP_EARLGREY_I2C1_BASE_ADDR), &i2c_1));
  CHECK_DIF_OK(
      dif_i2c_init(mmio_region_from_addr(TOP_EARLGREY_I2C2_BASE_ADDR), &i2c_2));
  CHECK_DIF_OK(dif_spi_device_init_handle(
      mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR), &spi_device));
  CHECK_DIF_OK(dif_spi_host_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_HOST0_BASE_ADDR), &spi_host_0));
  CHECK_DIF_OK(dif_spi_host_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_HOST1_BASE_ADDR), &spi_host_1));
  CHECK_DIF_OK(dif_pattgen_init(
      mmio_region_from_addr(TOP_EARLGREY_PATTGEN_BASE_ADDR), &pattgen));
  CHECK_DIF_OK(dif_pwm_init(
      mmio_region_from_addr(TOP_EARLGREY_PWM_AON_BASE_ADDR), &pwm));
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
}

static void configure_pinmux(void) {
  // Configure UART0 (console) and SW strapping pins.
  pinmux_testutils_init(&pinmux);

  // Configure GPIO max-power period indicator pin on IOA2
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoa2,
                                        kTopEarlgreyPinmuxOutselGpioGpio0));

  // UART1:
  //    RX on IOA4
  //    TX on IOA5
  CHECK_DIF_OK(dif_pinmux_input_select(&pinmux,
                                       kTopEarlgreyPinmuxPeripheralInUart1Rx,
                                       kTopEarlgreyPinmuxInselIoa4));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoa4,
                                        kTopEarlgreyPinmuxOutselConstantHighZ));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoa5,
                                        kTopEarlgreyPinmuxOutselUart1Tx));

  // UART2:
  //    RX on IOB4
  //    TX on IOB5
  CHECK_DIF_OK(dif_pinmux_input_select(&pinmux,
                                       kTopEarlgreyPinmuxPeripheralInUart2Rx,
                                       kTopEarlgreyPinmuxInselIob4));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIob4,
                                        kTopEarlgreyPinmuxOutselConstantHighZ));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIob5,
                                        kTopEarlgreyPinmuxOutselUart2Tx));

  // UART3:
  //    RX on IOA0
  //    TX on IOA1
  CHECK_DIF_OK(dif_pinmux_input_select(&pinmux,
                                       kTopEarlgreyPinmuxPeripheralInUart3Rx,
                                       kTopEarlgreyPinmuxInselIoa0));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoa0,
                                        kTopEarlgreyPinmuxOutselConstantHighZ));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoa1,
                                        kTopEarlgreyPinmuxOutselUart3Tx));

  // I2C0:
  //    SDA on IOA7
  //    SCL on IOA8
  CHECK_DIF_OK(dif_pinmux_input_select(&pinmux,
                                       kTopEarlgreyPinmuxPeripheralInI2c0Sda,
                                       kTopEarlgreyPinmuxInselIoa7));
  CHECK_DIF_OK(dif_pinmux_input_select(&pinmux,
                                       kTopEarlgreyPinmuxPeripheralInI2c0Scl,
                                       kTopEarlgreyPinmuxInselIoa8));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoa7,
                                        kTopEarlgreyPinmuxOutselI2c0Sda));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoa8,
                                        kTopEarlgreyPinmuxOutselI2c0Scl));

  // I2C1:
  //    SDA on IOB9
  //    SCL on IOB10
  CHECK_DIF_OK(dif_pinmux_input_select(&pinmux,
                                       kTopEarlgreyPinmuxPeripheralInI2c1Sda,
                                       kTopEarlgreyPinmuxInselIob9));
  CHECK_DIF_OK(dif_pinmux_input_select(&pinmux,
                                       kTopEarlgreyPinmuxPeripheralInI2c1Scl,
                                       kTopEarlgreyPinmuxInselIob10));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIob9,
                                        kTopEarlgreyPinmuxOutselI2c1Sda));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIob10,
                                        kTopEarlgreyPinmuxOutselI2c1Scl));

  // I2C2:
  //    SDA on IOB11
  //    SCL on IOB12
  CHECK_DIF_OK(dif_pinmux_input_select(&pinmux,
                                       kTopEarlgreyPinmuxPeripheralInI2c2Sda,
                                       kTopEarlgreyPinmuxInselIob11));
  CHECK_DIF_OK(dif_pinmux_input_select(&pinmux,
                                       kTopEarlgreyPinmuxPeripheralInI2c2Scl,
                                       kTopEarlgreyPinmuxInselIob12));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIob11,
                                        kTopEarlgreyPinmuxOutselI2c2Sda));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIob12,
                                        kTopEarlgreyPinmuxOutselI2c2Scl));

  // Enable pull-ups for SPI_HOST_0/1 data pins to avoid floating inputs.
  if (kDeviceType == kDeviceSimDV || kDeviceType == kDeviceSimVerilator) {
    pinmux_testutils_configure_pads(&pinmux, pinmux_pad_attributes,
                                    ARRAYSIZE(pinmux_pad_attributes));
  }

  // PATTGEN:
  //    Channel 0 PDA on IOR0
  //    Channel 0 PCL on IOR1
  //    Channel 1 PDA on IOR2
  //    Channel 1 PCL on IOR3
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIor0,
                                        kTopEarlgreyPinmuxOutselPattgenPda0Tx));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIor1,
                                        kTopEarlgreyPinmuxOutselPattgenPcl0Tx));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIor2,
                                        kTopEarlgreyPinmuxOutselPattgenPda1Tx));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIor3,
                                        kTopEarlgreyPinmuxOutselPattgenPcl1Tx));

  // PWM:
  //    Channel 0 on IOB1
  //    Channel 1 on IOB2
  //    Channel 2 on IOR5
  //    Channel 3 on IOR6
  //    Channel 4 on IOR7
  //    Channel 5 on IOR10
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIob1,
                                        kTopEarlgreyPinmuxOutselPwmAonPwm0));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIob2,
                                        kTopEarlgreyPinmuxOutselPwmAonPwm1));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIor5,
                                        kTopEarlgreyPinmuxOutselPwmAonPwm2));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIor6,
                                        kTopEarlgreyPinmuxOutselPwmAonPwm3));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIor7,
                                        kTopEarlgreyPinmuxOutselPwmAonPwm4));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIor10,
                                        kTopEarlgreyPinmuxOutselPwmAonPwm5));

  // SPI Host 1:
  //    CSB on IOB0
  //    SCK on IOB3
  //    SD0 on IOA2
  //    SD1 on IOR11
  //    SD2 on IOR12
  //    SD3 on IOR13
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIob0,
                                        kTopEarlgreyPinmuxOutselSpiHost1Csb));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIob3,
                                        kTopEarlgreyPinmuxOutselSpiHost1Sck));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIoa2,
                                        kTopEarlgreyPinmuxOutselSpiHost1Sd0));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIor11,
                                        kTopEarlgreyPinmuxOutselSpiHost1Sd1));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIor12,
                                        kTopEarlgreyPinmuxOutselSpiHost1Sd1));
  CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, kTopEarlgreyPinmuxMioOutIor13,
                                        kTopEarlgreyPinmuxOutselSpiHost1Sd1));
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInSpiHost1Sd0,
      kTopEarlgreyPinmuxInselIoa2));
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInSpiHost1Sd1,
      kTopEarlgreyPinmuxInselIor11));
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInSpiHost1Sd2,
      kTopEarlgreyPinmuxInselIor12));
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInSpiHost1Sd3,
      kTopEarlgreyPinmuxInselIor13));
}

/**
 * Configures adc_ctrl to continuously sample data (applying all filters across
 * both channels) in normal power mode, which is the most power intensive
 * sampling mode.
 */
static void configure_adc_ctrl_to_continuously_sample(void) {
  CHECK_DIF_OK(dif_adc_ctrl_configure(
      &adc_ctrl,
      (dif_adc_ctrl_config_t){
          .mode = kDifAdcCtrlNormalPowerScanMode,
          .power_up_time_aon_cycles = kAdcCtrlPowerUpTimeAonCycles,
          // Below configurations are unused, so set them to their reset values.
          .wake_up_time_aon_cycles = ADC_CTRL_ADC_PD_CTL_WAKEUP_TIME_MASK,
          .num_low_power_samples = ADC_CTRL_ADC_LP_SAMPLE_CTL_REG_RESVAL,
          .num_normal_power_samples = ADC_CTRL_ADC_SAMPLE_CTL_REG_RESVAL,
      }));
  for (size_t filter = 0; filter < ADC_CTRL_PARAM_NUM_ADC_FILTER; ++filter) {
    for (size_t channel = 0; channel < ADC_CTRL_PARAM_NUM_ADC_CHANNEL;
         ++channel) {
      CHECK_DIF_OK(dif_adc_ctrl_configure_filter(
          &adc_ctrl, (dif_adc_ctrl_channel_t)channel,
          (dif_adc_ctrl_filter_config_t){
              .filter = (dif_adc_ctrl_filter_t)filter,
              // Set max range.
              .min_voltage = 0,
              .max_voltage = ADC_CTRL_ADC_CHN0_FILTER_CTL_0_MAX_V_0_MASK,
              .in_range = true,
              .generate_wakeup_on_match = false,
              .generate_irq_on_match = false,
          },
          kDifToggleEnabled));
    }
  }
}

static void configure_entropy_complex(void) {
  // The (test) ROM enables the entropy complex, and to reconfigure it requires
  // temporarily disabling it.
  entropy_testutils_stop_all();

  CHECK_DIF_OK(dif_entropy_src_configure(
      &entropy_src,
      (dif_entropy_src_config_t){
          .fips_enable = true,
          .route_to_firmware = true,
          .bypass_conditioner = false,
          .single_bit_mode = kDifEntropySrcSingleBitModeDisabled,
          .health_test_threshold_scope = false,
          .health_test_window_size = 0x200,
          .alert_threshold = UINT16_MAX},
      kDifToggleDisabled));
  CHECK_DIF_OK(dif_entropy_src_health_test_configure(
      &entropy_src, (dif_entropy_src_health_test_config_t){
                        .test_type = kDifEntropySrcTestRepetitionCount,
                        .high_threshold = UINT16_MAX,
                        .low_threshold = 0}));
  CHECK_DIF_OK(dif_entropy_src_health_test_configure(
      &entropy_src, (dif_entropy_src_health_test_config_t){
                        .test_type = kDifEntropySrcTestRepetitionCountSymbol,
                        .high_threshold = UINT16_MAX,
                        .low_threshold = 0}));
  CHECK_DIF_OK(dif_entropy_src_health_test_configure(
      &entropy_src, (dif_entropy_src_health_test_config_t){
                        .test_type = kDifEntropySrcTestAdaptiveProportion,
                        .high_threshold = UINT16_MAX,
                        .low_threshold = 0}));
  CHECK_DIF_OK(dif_entropy_src_health_test_configure(
      &entropy_src, (dif_entropy_src_health_test_config_t){
                        .test_type = kDifEntropySrcTestBucket,
                        .high_threshold = UINT16_MAX,
                        .low_threshold = 0}));
  CHECK_DIF_OK(dif_entropy_src_health_test_configure(
      &entropy_src, (dif_entropy_src_health_test_config_t){
                        .test_type = kDifEntropySrcTestMarkov,
                        .high_threshold = UINT16_MAX,
                        .low_threshold = 0}));
  CHECK_DIF_OK(dif_entropy_src_fw_override_configure(
      &entropy_src,
      (dif_entropy_src_fw_override_config_t){
          .entropy_insert_enable = false,
          .buffer_threshold = ENTROPY_SRC_OBSERVE_FIFO_THRESH_REG_RESVAL,
      },
      kDifToggleDisabled));

  CHECK_DIF_OK(dif_csrng_configure(&csrng));

  dif_edn_seed_material_t edn_empty_seed = {
      .len = 0,
  };
  dif_edn_seed_material_t edn_384_bit_seed = {
      .len = 12,
      .data = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12},
  };
  dif_edn_auto_params_t edn_auto_params = {
      // EDN0 provides lower-quality entropy. Let one generate command return
      // eight 128-bit blocks, and reseed every 32 generates.
      .instantiate_cmd =
          {
              .cmd = csrng_cmd_header_build(kCsrngAppCmdInstantiate,
                                            kDifCsrngEntropySrcToggleEnable,
                                            /*cmd_len=*/12,
                                            /*generate_len=*/0),
              .seed_material = edn_384_bit_seed,
          },
      .reseed_cmd =
          {
              .cmd = csrng_cmd_header_build(kCsrngAppCmdReseed,
                                            kDifCsrngEntropySrcToggleEnable,
                                            /*cmd_len=*/12, /*generate_len=*/0),
              .seed_material = edn_384_bit_seed,
          },
      .generate_cmd =
          {
              .cmd = csrng_cmd_header_build(kCsrngAppCmdGenerate,
                                            kDifCsrngEntropySrcToggleEnable,
                                            /*cmd_len=*/0,
                                            /*generate_len=*/8),
              .seed_material = edn_empty_seed,
          },
      .reseed_interval = 0,
  };
  edn_auto_params.reseed_interval = kEdn0ReseedInterval;
  CHECK_DIF_OK(dif_edn_set_auto_mode(&edn_0, edn_auto_params));
  edn_auto_params.reseed_interval = kEdn1ReseedInterval;
  CHECK_DIF_OK(dif_edn_set_auto_mode(&edn_1, edn_auto_params));
  CHECK_DIF_OK(dif_edn_configure(&edn_0));
  CHECK_DIF_OK(dif_edn_configure(&edn_1));
}

static void configure_aes(void) {
  // Prepare and load AES key shares.
  uint8_t aes_key_share0[sizeof(kAesModesKey256)];
  for (size_t i = 0; i < sizeof(kAesModesKey256); ++i) {
    aes_key_share0[i] = kAesModesKey256[i] ^ kAesKeyShare1[i];
  }
  dif_aes_key_share_t aes_key;
  memcpy(aes_key.share0, aes_key_share0, sizeof(aes_key.share0));
  memcpy(aes_key.share1, kAesKeyShare1, sizeof(aes_key.share1));

  // Prepare and load AES IV.
  dif_aes_iv_t aes_iv;
  memcpy(aes_iv.iv, kAesModesIvCbc, sizeof(aes_iv.iv));

  // Setup AES in automatic, 256-bit SW provided key, CBC encryption mode.
  // Additionally, we want to keep the entropy complex busing by constantly
  // reseeding PRNGs.
  dif_aes_transaction_t aes_transaction_cfg = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeCbc,
      .key_len = kDifAesKey256,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPer64Block,
      .manual_operation = kDifAesManualOperationManual,
      .reseed_on_key_change = false,
      .ctrl_aux_lock = false,
  };

  // Start the AES operation. Since we are in manual-mode, the encryption will
  // not start until plain text data is loaded into the appropriate CSRs, the
  // encryption operation is triggered.
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true,
                                kTestTimeoutMicros);
  CHECK_DIF_OK(dif_aes_start(&aes, &aes_transaction_cfg, &aes_key, &aes_iv));
}

static void configure_hmac(void) {
  dif_hmac_transaction_t hmac_transaction_cfg = {
      .digest_endianness = kDifHmacEndiannessLittle,
      .message_endianness = kDifHmacEndiannessLittle,
  };
  CHECK_DIF_OK(dif_hmac_mode_hmac_start(&hmac, kHmacKey, hmac_transaction_cfg));
}

static void configure_kmac(void) {
  dif_kmac_config_t kmac_cfg = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeEdn,
      .entropy_fast_process = kDifToggleDisabled,
      .entropy_hash_threshold = kKmacEntropyHashThreshold,
      .entropy_wait_timer = kKmacEntropyWaitTimer,
      .entropy_prescaler = kKmacEntropyPrescaler,
      .message_big_endian = false,
      .output_big_endian = false,
      .sideload = false,
      .msg_mask = false,
  };
  CHECK_DIF_OK(dif_kmac_configure(&kmac, kmac_cfg));
}

static void configure_uart(dif_uart_t *uart) {
  CHECK_DIF_OK(
      dif_uart_configure(uart, (dif_uart_config_t){
                                   .baudrate = kUartBaudrate,
                                   .clk_freq_hz = kClockFreqPeripheralHz,
                                   .parity_enable = kDifToggleEnabled,
                                   .parity = kDifUartParityEven,
                                   .tx_enable = kDifToggleDisabled,
                                   .rx_enable = kDifToggleDisabled,
                               }));
  CHECK_DIF_OK(
      dif_uart_loopback_set(uart, kDifUartLoopbackSystem, kDifToggleEnabled));
}

static void configure_i2c(dif_i2c_t *i2c, uint8_t device_addr_0,
                          uint8_t device_addr_1) {
  dif_i2c_config_t config;

  CHECK_DIF_OK(dif_i2c_compute_timing(
      (dif_i2c_timing_config_t){
          .lowest_target_device_speed = kDifI2cSpeedFastPlus,
          .clock_period_nanos = peripheral_clock_period_ns,
          .sda_rise_nanos = kI2cSdaRiseFallTimeNs,
          .sda_fall_nanos = kI2cSdaRiseFallTimeNs,
          .scl_period_nanos = kI2cSclPeriodNs},
      &config));
  CHECK_DIF_OK(dif_i2c_configure(i2c, config));
  dif_i2c_id_t id_0 = {.mask = kI2cDeviceMask, .address = device_addr_0};
  dif_i2c_id_t id_1 = {.mask = kI2cDeviceMask, .address = device_addr_1};
  CHECK_DIF_OK(dif_i2c_set_device_id(i2c, &id_0, &id_1));
  CHECK_DIF_OK(dif_i2c_line_loopback_set_enabled(i2c, kDifToggleEnabled));
}

static void configure_spi_host(const dif_spi_host_t *spi_host, bool enable) {
  CHECK_DIF_OK(dif_spi_host_configure(
      spi_host, (dif_spi_host_config_t){
                    .spi_clock = kClockFreqHiSpeedPeripheralHz / 2,
                    .peripheral_clock_freq_hz = kClockFreqHiSpeedPeripheralHz,
                    .chip_select =
                        {
                            .idle = 2,
                            .trail = 2,
                            .lead = 2,
                        },
                }));
  CHECK_DIF_OK(dif_spi_host_output_set_enabled(spi_host, /*enabled=*/enable));
}

void configure_pattgen(void) {
  for (size_t i = 0; i < ARRAYSIZE(pattgen_channels); ++i) {
    CHECK_DIF_OK(dif_pattgen_channel_set_enabled(&pattgen, pattgen_channels[i],
                                                 kDifToggleDisabled));
    CHECK_DIF_OK(dif_pattgen_configure_channel(
        &pattgen, pattgen_channels[i],
        (dif_pattgen_channel_config_t){
            .polarity = kDifPattgenPolarityHigh,
            .clock_divisor = kPattgenClockDivisor,
            .seed_pattern_lower_word = kPattgenSeedPatternLowerWord,
            .seed_pattern_upper_word = kPattgenSeedPatternUpperWord,
            .seed_pattern_length = kPattgenSeedPatternLength,
            .num_pattern_repetitions = kPattgenNumPatternRepetitions,

        }));
  }
}

void configure_pwm(void) {
  CHECK_DIF_OK(
      dif_pwm_configure(&pwm, (dif_pwm_config_t){
                                  .clock_divisor = kPwmClockDivisor,
                                  .beats_per_pulse_cycle = kPwmBeatsPerCycle,
                              }));
  for (size_t i = 0; i < PWM_PARAM_N_OUTPUTS; ++i) {
    CHECK_DIF_OK(
        dif_pwm_channel_set_enabled(&pwm, pwm_channels[i], kDifToggleDisabled));
    CHECK_DIF_OK(
        dif_pwm_configure_channel(&pwm, pwm_channels[i],
                                  (dif_pwm_channel_config_t){
                                      .duty_cycle_a = kPwmOnBeats,
                                      .duty_cycle_b = 0,  // unused
                                      .phase_delay = kPwmPhaseDelayBeats,
                                      .mode = kDifPwmModeFirmware,
                                      .polarity = kDifPwmPolarityActiveHigh,
                                      .blink_parameter_x = 0,  // unused
                                      .blink_parameter_y = 0,  // unused
                                  }));
    CHECK_DIF_OK(
        dif_pwm_channel_set_enabled(&pwm, pwm_channels[i], kDifToggleEnabled));
  }
}

static void crypto_data_load_task(void *task_parameters) {
  LOG_INFO("Loading crypto block FIFOs with data ...");
  // Load data into AES block.
  dif_aes_data_t aes_plain_text;
  memcpy(aes_plain_text.data, kAesModesPlainText, sizeof(aes_plain_text.data));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true,
                                kTestTimeoutMicros);
  CHECK_DIF_OK(dif_aes_load_data(&aes, aes_plain_text));

  // Load data into HMAC block.
  hmac_testutils_push_message(&hmac, kHmacRefData, sizeof(kHmacRefData));
  hmac_testutils_check_message_length(&hmac, sizeof(kHmacRefData) * 8);

  // Load data into KMAC block.
  dif_kmac_customization_string_t kmac_customization_string;
  CHECK_DIF_OK(dif_kmac_customization_string_init("Power Virus Test", 16,
                                                  &kmac_customization_string));
  CHECK_DIF_OK(dif_kmac_mode_kmac_start(
      &kmac, &kmac_operation_state, kDifKmacModeKmacLen256, kKmacDigestLength,
      &kKmacKey, &kmac_customization_string));
  CHECK_DIF_OK(dif_kmac_absorb(&kmac, &kmac_operation_state, kKmacMessage,
                               kKmacMessageLength, NULL));

  OTTF_TASK_DELETE_SELF_OR_DIE;
}

static void comms_data_load_task(void *task_parameters) {
  LOG_INFO("Loading communication block FIFOs with data ...");
  size_t bytes_written;
  CHECK(ARRAYSIZE(kUartMessage) == kUartFifoDepth);
  CHECK(ARRAYSIZE(kI2cMessage) == I2C_PARAM_FIFO_DEPTH);

  // Load data into UART FIFOs.
  for (size_t i = 0; i < ARRAYSIZE(uart_handles); ++i) {
    bytes_written = 0;
    CHECK_DIF_OK(dif_uart_bytes_send(uart_handles[i], kUartMessage,
                                     ARRAYSIZE(kUartMessage), &bytes_written));
    CHECK(bytes_written == ARRAYSIZE(kUartMessage));
  }

  // Load data into I2C FIFOs.
  dif_i2c_status_t i2c_status;
  for (size_t i = 0; i < ARRAYSIZE(i2c_handles); ++i) {
    i2c_testutils_wr(i2c_handles[i], /*addr=*/i, I2C_PARAM_FIFO_DEPTH,
                     kI2cMessage, /*skip_stop=*/false);
    CHECK_DIF_OK(dif_i2c_get_status(i2c_handles[i], &i2c_status));
    CHECK(i2c_status.fmt_fifo_full);
  }

  // Load data into SPI host (1; as 0 is used in passthrough mode) FIFO.
  uint32_t spi_host_tx_data[SPI_HOST_PARAM_TX_DEPTH];
  for (size_t i = 0; i < SPI_HOST_PARAM_TX_DEPTH; ++i) {
    spi_host_tx_data[i] = kSpiHost1TxDataWord;
  }
  dif_spi_host_segment_t spi_host_tx_segment = {
      .type = kDifSpiHostSegmentTypeTx,
      .tx = {
          .width = kDifSpiHostWidthQuad,
          .buf = (void *)&spi_host_tx_data,
          .length = ARRAYSIZE(spi_host_tx_data),
      }};
  CHECK_DIF_OK(dif_spi_host_transaction(&spi_host_1, kSpiHost1Csid,
                                        &spi_host_tx_segment, 1));

  OTTF_TASK_DELETE_SELF_OR_DIE;
}

static void max_power_task(void *task_parameters) {
  LOG_INFO("Starting the max power task ...");
  // ***************************************************************************
  // Trigger all chip operations.
  //
  // Note: We trigger the activations of each operation manually, rather than
  // use the DIFs, so that we can maximize the time overlap between all
  // operations.
  // ***************************************************************************

  // Prepare KMAC for squeeze command. Note, below code is derived from the
  // KMAC DIF `dif_kmac_sqeeze()`.
  CHECK(!kmac_operation_state.squeezing);
  if (kmac_operation_state.append_d) {
    // The KMAC operation requires that the output length (d) in bits be right
    // encoded and appended to the end of the message.
    // Note: kDifKmacMaxOutputLenWords could be reduced to make this code
    // simpler. For example, a maximum of `(UINT16_MAX - 32) / 32` (just under
    // 8 KiB) would mean that d is guaranteed to be less than 0xFFFF.
    uint32_t d = kmac_operation_state.d * 32;
    int len = 1 + (d > 0xFF) + (d > 0xFFFF) + (d > 0xFFFFFF);
    int shift = (len - 1) * 8;
    while (shift >= 8) {
      mmio_region_write8(kmac.base_addr, KMAC_MSG_FIFO_REG_OFFSET,
                         (uint8_t)(d >> shift));
      shift -= 8;
    }
    mmio_region_write8(kmac.base_addr, KMAC_MSG_FIFO_REG_OFFSET, (uint8_t)d);
    mmio_region_write8(kmac.base_addr, KMAC_MSG_FIFO_REG_OFFSET, (uint8_t)len);
  }

  // Prepare AES and HMAC trigger / process commands.
  uint32_t aes_trigger_reg = bitfield_bit32_write(0, kDifAesTriggerStart, true);
  uint32_t hmac_cmd_reg =
      mmio_region_read32(hmac.base_addr, HMAC_CMD_REG_OFFSET);
  hmac_cmd_reg =
      bitfield_bit32_write(hmac_cmd_reg, HMAC_CMD_HASH_PROCESS_BIT, true);
  uint32_t kmac_cmd_reg =
      bitfield_field32_write(0, KMAC_CMD_CMD_FIELD, KMAC_CMD_CMD_VALUE_PROCESS);

  // Prepare UART, I2C, SPI host enablement commands (note, all configurations
  // between each IP instance should be configured the same).
  uint32_t uart_ctrl_reg =
      mmio_region_read32(uart_1.base_addr, UART_CTRL_REG_OFFSET);
  uart_ctrl_reg = bitfield_bit32_write(uart_ctrl_reg, UART_CTRL_TX_BIT, true);
  uart_ctrl_reg = bitfield_bit32_write(uart_ctrl_reg, UART_CTRL_RX_BIT, true);
  uint32_t i2c_ctrl_reg =
      mmio_region_read32(i2c_0.base_addr, I2C_CTRL_REG_OFFSET);
  i2c_ctrl_reg =
      bitfield_bit32_write(i2c_ctrl_reg, I2C_CTRL_ENABLEHOST_BIT, true);
  uint32_t spi_host_1_ctrl_reg =
      mmio_region_read32(spi_host_1.base_addr, SPI_HOST_CONTROL_REG_OFFSET);
  spi_host_1_ctrl_reg = bitfield_bit32_write(
      spi_host_1_ctrl_reg, SPI_HOST_CONTROL_OUTPUT_EN_BIT, true);

  // Prepare pattgen enablement command.
  uint32_t pattgen_ctrl_reg =
      mmio_region_read32(pattgen.base_addr, PATTGEN_CTRL_REG_OFFSET);
  pattgen_ctrl_reg =
      bitfield_bit32_write(pattgen_ctrl_reg, PATTGEN_CTRL_ENABLE_CH0_BIT, true);
  pattgen_ctrl_reg =
      bitfield_bit32_write(pattgen_ctrl_reg, PATTGEN_CTRL_ENABLE_CH1_BIT, true);

  // Enable all UARTs and I2Cs.
  mmio_region_write32(uart_1.base_addr, UART_CTRL_REG_OFFSET, uart_ctrl_reg);
  mmio_region_write32(uart_2.base_addr, UART_CTRL_REG_OFFSET, uart_ctrl_reg);
  mmio_region_write32(uart_3.base_addr, UART_CTRL_REG_OFFSET, uart_ctrl_reg);
  mmio_region_write32(i2c_0.base_addr, I2C_CTRL_REG_OFFSET, i2c_ctrl_reg);
  mmio_region_write32(i2c_1.base_addr, I2C_CTRL_REG_OFFSET, i2c_ctrl_reg);
  mmio_region_write32(i2c_2.base_addr, I2C_CTRL_REG_OFFSET, i2c_ctrl_reg);

  // Enable pattgen.
  mmio_region_write32(pattgen.base_addr, PATTGEN_CTRL_REG_OFFSET,
                      pattgen_ctrl_reg);

  // Enable SPI host (1).
  mmio_region_write32(spi_host_1.base_addr, SPI_HOST_CONTROL_REG_OFFSET,
                      spi_host_1_ctrl_reg);

  // Issue HMAC process, KMAC squeeze, and AES trigger commands.
  mmio_region_write32(hmac.base_addr, HMAC_CMD_REG_OFFSET, hmac_cmd_reg);
  kmac_operation_state.squeezing = true;
  mmio_region_write32(kmac.base_addr, KMAC_CMD_REG_OFFSET, kmac_cmd_reg);
  mmio_region_write32(aes.base_addr, AES_TRIGGER_REG_OFFSET, aes_trigger_reg);

  // Toggle GPIO pin to indicate we are in max power consumption.
  CHECK_DIF_OK(dif_gpio_write(&gpio, 0, true));
  // TODO (#14814): confirm AES is the fastest throughput cryto block.
  // Otherwise, wait for that block to finish processing instead.
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusOutputValid, true,
                                kTestTimeoutMicros);
  CHECK_DIF_OK(dif_gpio_write(&gpio, 0, false));

  // ***************************************************************************
  // Check operation results.
  // ***************************************************************************
  uint8_t received_uart_data[kUartFifoDepth];
  size_t num_uart_rx_bytes;
  for (size_t i = 0; i < ARRAYSIZE(uart_handles); ++i) {
    CHECK_DIF_OK(
        dif_uart_rx_bytes_available(uart_handles[i], &num_uart_rx_bytes));
    // Note, we don't care if all bytes have been transmitted out of the UART
    // by the time the fastest processing crypto block (i.e., the AES) has
    // completed. Likely, we won't have transmitted all data since the UART is
    // quite a bit slower. We just check that what was transmitted is correct.
    memset((void *)received_uart_data, 0, kUartFifoDepth);
    CHECK_DIF_OK(dif_uart_bytes_receive(uart_handles[i], num_uart_rx_bytes,
                                        received_uart_data, NULL));
    CHECK_ARRAYS_EQ(received_uart_data, kUartMessage, num_uart_rx_bytes);
  }

  OTTF_TASK_DELETE_SELF_OR_DIE;
}

static void check_otp_csr_configs(void) {
  dif_flash_ctrl_region_properties_t default_properties;
  CHECK_DIF_OK(dif_flash_ctrl_get_default_region_properties(
      &flash_ctrl, &default_properties));
  CHECK(default_properties.scramble_en == kMultiBitBool4False);
  CHECK(default_properties.ecc_en == kMultiBitBool4False);
  CHECK(default_properties.high_endurance_en == kMultiBitBool4False);
}

bool test_main(void) {
  peripheral_clock_period_ns =
      udiv64_slow(1000000000, kClockFreqPeripheralHz, NULL);
  // Note: DO NOT change this message string without updating the DV testbench.
  LOG_INFO("Computed peripheral clock period.");

  // ***************************************************************************
  // Initialize and configure all IPs.
  // ***************************************************************************
  init_peripheral_handles();
  configure_pinmux();
  // Clear GPIO pin 0 (max power indicator pin).
  CHECK_DIF_OK(
      dif_gpio_output_set_enabled(&gpio, /*pin=*/0, kDifToggleEnabled));
  configure_adc_ctrl_to_continuously_sample();
  configure_entropy_complex();
  configure_aes();
  configure_hmac();
  configure_kmac();
  configure_uart(&uart_1);
  configure_uart(&uart_2);
  configure_uart(&uart_3);
  configure_i2c(&i2c_0, kI2c0DeviceAddress0, kI2c0DeviceAddress1);
  configure_i2c(&i2c_1, kI2c1DeviceAddress0, kI2c1DeviceAddress1);
  configure_i2c(&i2c_2, kI2c2DeviceAddress0, kI2c2DeviceAddress1);
  configure_spi_host(&spi_host_0, /*enable=*/true);
  // We don't enable SPI host 1 just yet, as we want to pre-load its FIFO with
  // data before enabling it at the last moment, to initiate max power draw.
  configure_spi_host(&spi_host_1, /*enable=*/false);
  spi_device_testutils_configure_passthrough(&spi_device, /*filters=*/0,
                                             /*upload_write_commands=*/false);
  configure_pattgen();
  configure_pwm();
  LOG_INFO("All IPs configured.");

  // ***************************************************************************
  // Check OTP configurations propagated to CSRs.
  // ***************************************************************************
  check_otp_csr_configs();

  // ***************************************************************************
  // Kick off test tasks.
  // ***************************************************************************
  CHECK(ottf_task_create(crypto_data_load_task, "CryptoDataLoadTask",
                         kOttfFreeRtosMinStackSize, 1));
  CHECK(ottf_task_create(comms_data_load_task, "CommsDataLoadTask",
                         kOttfFreeRtosMinStackSize, 1));
  CHECK(ottf_task_create(max_power_task, "MaxPowerTask",
                         kOttfFreeRtosMinStackSize, 1));

  // ***************************************************************************
  // Yield control flow to the highest priority task in the run queue. Since
  // the tasks created above all have a higher priority level than the current
  // "test_main" task, and no tasks block, execution will not be returned to
  // the current task until the above tasks have been deleted.
  // ***************************************************************************
  LOG_INFO("Yielding execution to another task.");
  ottf_task_yield();

  return true;
}
