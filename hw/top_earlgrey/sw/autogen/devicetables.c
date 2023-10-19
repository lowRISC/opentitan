// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/devicetables/dt.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "hw/top_earlgrey/sw/autogen/devicetables/dt_alert_handler.h"
#include "hw/top_earlgrey/sw/autogen/devicetables/dt_clkmgr.h"
#include "hw/top_earlgrey/sw/autogen/devicetables/dt_flash_ctrl.h"
#include "hw/top_earlgrey/sw/autogen/devicetables/dt_pinmux.h"
#include "hw/top_earlgrey/sw/autogen/devicetables/dt_pwrmgr.h"
#include "hw/top_earlgrey/sw/autogen/devicetables/dt_rstmgr.h"
#include "hw/top_earlgrey/sw/autogen/devicetables/dt_rv_plic.h"
#include "sw/device/lib/devicetables/dt_adc_ctrl.h"
#include "sw/device/lib/devicetables/dt_aes.h"
#include "sw/device/lib/devicetables/dt_aon_timer.h"
#include "sw/device/lib/devicetables/dt_csrng.h"
#include "sw/device/lib/devicetables/dt_edn.h"
#include "sw/device/lib/devicetables/dt_entropy_src.h"
#include "sw/device/lib/devicetables/dt_gpio.h"
#include "sw/device/lib/devicetables/dt_hmac.h"
#include "sw/device/lib/devicetables/dt_i2c.h"
#include "sw/device/lib/devicetables/dt_keymgr.h"
#include "sw/device/lib/devicetables/dt_kmac.h"
#include "sw/device/lib/devicetables/dt_lc_ctrl.h"
#include "sw/device/lib/devicetables/dt_otbn.h"
#include "sw/device/lib/devicetables/dt_otp_ctrl.h"
#include "sw/device/lib/devicetables/dt_pattgen.h"
#include "sw/device/lib/devicetables/dt_pwm.h"
#include "sw/device/lib/devicetables/dt_rom_ctrl.h"
#include "sw/device/lib/devicetables/dt_rv_core_ibex.h"
#include "sw/device/lib/devicetables/dt_rv_dm.h"
#include "sw/device/lib/devicetables/dt_rv_timer.h"
#include "sw/device/lib/devicetables/dt_spi_device.h"
#include "sw/device/lib/devicetables/dt_spi_host.h"
#include "sw/device/lib/devicetables/dt_sram_ctrl.h"
#include "sw/device/lib/devicetables/dt_sysrst_ctrl.h"
#include "sw/device/lib/devicetables/dt_uart.h"
#include "sw/device/lib/devicetables/dt_usbdev.h"

//#include <assert.h>
#include <stdint.h>

// Device tables for adc_ctrl
_Static_assert(kDtAdcCtrlRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtAdcCtrlClockCount == 2, "Clock count mismatch");
_Static_assert(kDtAdcCtrlIrqTypeCount == 1, "IRQ count mismatch");

typedef struct dt_adc_ctrl_info {
  uint32_t base_addrs[kDtAdcCtrlRegBlockCount];
  dt_clock_t clocks[kDtAdcCtrlClockCount];
  uint32_t irqs[kDtAdcCtrlIrqTypeCount];
} dt_adc_ctrl_info_t;

static const dt_adc_ctrl_info_t dev_table_adc_ctrl[kDtDeviceCountAdcCtrl] = {
    // Properties for adc_ctrl_aon
    {
        .base_addrs = {
            0x40440000,
        },
        .clocks = {
            [kDtAdcCtrlClockClk] = kTopEarlgreyClockSrcIoDiv4,
            [kDtAdcCtrlClockAon] = kTopEarlgreyClockSrcAon,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdAdcCtrlAonMatchDone,
        },
    },
};
// Device tables for aes
_Static_assert(kDtAesRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtAesClockCount == 2, "Clock count mismatch");

typedef struct dt_aes_info {
  uint32_t base_addrs[kDtAesRegBlockCount];
  dt_clock_t clocks[kDtAesClockCount];
} dt_aes_info_t;

static const dt_aes_info_t dev_table_aes[kDtDeviceCountAes] = {
    // Properties for aes
    {
        .base_addrs = {
            0x41100000,
        },
        .clocks = {
            [kDtAesClockClk] = kTopEarlgreyClockSrcMain,
            [kDtAesClockEdn] = kTopEarlgreyClockSrcMain,
        },
    },
};
// Device tables for alert_handler
_Static_assert(kDtAlertHandlerRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtAlertHandlerClockCount == 2, "Clock count mismatch");
_Static_assert(kDtAlertHandlerIrqTypeCount == 4, "IRQ count mismatch");

typedef struct dt_alert_handler_info {
  uint32_t base_addrs[kDtAlertHandlerRegBlockCount];
  dt_clock_t clocks[kDtAlertHandlerClockCount];
  uint32_t irqs[kDtAlertHandlerIrqTypeCount];
} dt_alert_handler_info_t;

static const dt_alert_handler_info_t dev_table_alert_handler[kDtDeviceCountAlertHandler] = {
    // Properties for alert_handler
    {
        .base_addrs = {
            0x40150000,
        },
        .clocks = {
            [kDtAlertHandlerClockClk] = kTopEarlgreyClockSrcIoDiv4,
            [kDtAlertHandlerClockEdn] = kTopEarlgreyClockSrcMain,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdAlertHandlerClassa,
            kTopEarlgreyPlicIrqIdAlertHandlerClassb,
            kTopEarlgreyPlicIrqIdAlertHandlerClassc,
            kTopEarlgreyPlicIrqIdAlertHandlerClassd,
        },
    },
};
// Device tables for aon_timer
_Static_assert(kDtAonTimerRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtAonTimerClockCount == 2, "Clock count mismatch");
_Static_assert(kDtAonTimerIrqTypeCount == 2, "IRQ count mismatch");

typedef struct dt_aon_timer_info {
  uint32_t base_addrs[kDtAonTimerRegBlockCount];
  dt_clock_t clocks[kDtAonTimerClockCount];
  uint32_t irqs[kDtAonTimerIrqTypeCount];
} dt_aon_timer_info_t;

static const dt_aon_timer_info_t dev_table_aon_timer[kDtDeviceCountAonTimer] = {
    // Properties for aon_timer_aon
    {
        .base_addrs = {
            0x40470000,
        },
        .clocks = {
            [kDtAonTimerClockClk] = kTopEarlgreyClockSrcIoDiv4,
            [kDtAonTimerClockAon] = kTopEarlgreyClockSrcAon,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired,
            kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark,
        },
    },
};
// Device tables for ast
// TODO: Handle tables for top_reggen types
// Device tables for clkmgr
_Static_assert(kDtClkmgrRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtClkmgrClockCount == 5, "Clock count mismatch");

typedef struct dt_clkmgr_info {
  uint32_t base_addrs[kDtClkmgrRegBlockCount];
  dt_clock_t clocks[kDtClkmgrClockCount];
} dt_clkmgr_info_t;

static const dt_clkmgr_info_t dev_table_clkmgr[kDtDeviceCountClkmgr] = {
    // Properties for clkmgr_aon
    {
        .base_addrs = {
            0x40420000,
        },
        .clocks = {
            [kDtClkmgrClockClk] = kTopEarlgreyClockSrcIoDiv4,
            [kDtClkmgrClockMain] = kTopEarlgreyClockSrcMain,
            [kDtClkmgrClockIo] = kTopEarlgreyClockSrcIo,
            [kDtClkmgrClockUsb] = kTopEarlgreyClockSrcUsb,
            [kDtClkmgrClockAon] = kTopEarlgreyClockSrcAon,
        },
    },
};
// Device tables for csrng
_Static_assert(kDtCsrngRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtCsrngClockCount == 1, "Clock count mismatch");
_Static_assert(kDtCsrngIrqTypeCount == 4, "IRQ count mismatch");

typedef struct dt_csrng_info {
  uint32_t base_addrs[kDtCsrngRegBlockCount];
  dt_clock_t clocks[kDtCsrngClockCount];
  uint32_t irqs[kDtCsrngIrqTypeCount];
} dt_csrng_info_t;

static const dt_csrng_info_t dev_table_csrng[kDtDeviceCountCsrng] = {
    // Properties for csrng
    {
        .base_addrs = {
            0x41150000,
        },
        .clocks = {
            [kDtCsrngClockClk] = kTopEarlgreyClockSrcMain,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdCsrngCsCmdReqDone,
            kTopEarlgreyPlicIrqIdCsrngCsEntropyReq,
            kTopEarlgreyPlicIrqIdCsrngCsHwInstExc,
            kTopEarlgreyPlicIrqIdCsrngCsFatalErr,
        },
    },
};
// Device tables for edn
_Static_assert(kDtEdnRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtEdnClockCount == 1, "Clock count mismatch");
_Static_assert(kDtEdnIrqTypeCount == 2, "IRQ count mismatch");

typedef struct dt_edn_info {
  uint32_t base_addrs[kDtEdnRegBlockCount];
  dt_clock_t clocks[kDtEdnClockCount];
  uint32_t irqs[kDtEdnIrqTypeCount];
} dt_edn_info_t;

static const dt_edn_info_t dev_table_edn[kDtDeviceCountEdn] = {
    // Properties for edn0
    {
        .base_addrs = {
            0x41170000,
        },
        .clocks = {
            [kDtEdnClockClk] = kTopEarlgreyClockSrcMain,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdEdn0EdnCmdReqDone,
            kTopEarlgreyPlicIrqIdEdn0EdnFatalErr,
        },
    },
    // Properties for edn1
    {
        .base_addrs = {
            0x41180000,
        },
        .clocks = {
            [kDtEdnClockClk] = kTopEarlgreyClockSrcMain,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdEdn1EdnCmdReqDone,
            kTopEarlgreyPlicIrqIdEdn1EdnFatalErr,
        },
    },
};
// Device tables for entropy_src
_Static_assert(kDtEntropySrcRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtEntropySrcClockCount == 1, "Clock count mismatch");
_Static_assert(kDtEntropySrcIrqTypeCount == 4, "IRQ count mismatch");

typedef struct dt_entropy_src_info {
  uint32_t base_addrs[kDtEntropySrcRegBlockCount];
  dt_clock_t clocks[kDtEntropySrcClockCount];
  uint32_t irqs[kDtEntropySrcIrqTypeCount];
} dt_entropy_src_info_t;

static const dt_entropy_src_info_t dev_table_entropy_src[kDtDeviceCountEntropySrc] = {
    // Properties for entropy_src
    {
        .base_addrs = {
            0x41160000,
        },
        .clocks = {
            [kDtEntropySrcClockClk] = kTopEarlgreyClockSrcMain,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdEntropySrcEsEntropyValid,
            kTopEarlgreyPlicIrqIdEntropySrcEsHealthTestFailed,
            kTopEarlgreyPlicIrqIdEntropySrcEsObserveFifoReady,
            kTopEarlgreyPlicIrqIdEntropySrcEsFatalErr,
        },
    },
};
// Device tables for flash_ctrl
_Static_assert(kDtFlashCtrlRegBlockCount == 3, "Reg block count mismatch");
_Static_assert(kDtFlashCtrlClockCount == 2, "Clock count mismatch");
_Static_assert(kDtFlashCtrlIrqTypeCount == 6, "IRQ count mismatch");

typedef struct dt_flash_ctrl_info {
  uint32_t base_addrs[kDtFlashCtrlRegBlockCount];
  dt_clock_t clocks[kDtFlashCtrlClockCount];
  uint32_t irqs[kDtFlashCtrlIrqTypeCount];
} dt_flash_ctrl_info_t;

static const dt_flash_ctrl_info_t dev_table_flash_ctrl[kDtDeviceCountFlashCtrl] = {
    // Properties for flash_ctrl
    {
        .base_addrs = {
            0x41000000,
            0x41008000,
            0x20000000,
        },
        .clocks = {
            [kDtFlashCtrlClockClk] = kTopEarlgreyClockSrcMain,
            [kDtFlashCtrlClockOtp] = kTopEarlgreyClockSrcIoDiv4,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdFlashCtrlProgEmpty,
            kTopEarlgreyPlicIrqIdFlashCtrlProgLvl,
            kTopEarlgreyPlicIrqIdFlashCtrlRdFull,
            kTopEarlgreyPlicIrqIdFlashCtrlRdLvl,
            kTopEarlgreyPlicIrqIdFlashCtrlOpDone,
            kTopEarlgreyPlicIrqIdFlashCtrlCorrErr,
        },
    },
};
// Device tables for gpio
_Static_assert(kDtGpioRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtGpioClockCount == 1, "Clock count mismatch");
_Static_assert(kDtGpioIrqTypeCount == 32, "IRQ count mismatch");

typedef struct dt_gpio_info {
  uint32_t base_addrs[kDtGpioRegBlockCount];
  dt_clock_t clocks[kDtGpioClockCount];
  uint32_t irqs[kDtGpioIrqTypeCount];
} dt_gpio_info_t;

static const dt_gpio_info_t dev_table_gpio[kDtDeviceCountGpio] = {
    // Properties for gpio
    {
        .base_addrs = {
            0x40040000,
        },
        .clocks = {
            [kDtGpioClockClk] = kTopEarlgreyClockSrcIoDiv4,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdGpioGpio0,
            kTopEarlgreyPlicIrqIdGpioGpio1,
            kTopEarlgreyPlicIrqIdGpioGpio2,
            kTopEarlgreyPlicIrqIdGpioGpio3,
            kTopEarlgreyPlicIrqIdGpioGpio4,
            kTopEarlgreyPlicIrqIdGpioGpio5,
            kTopEarlgreyPlicIrqIdGpioGpio6,
            kTopEarlgreyPlicIrqIdGpioGpio7,
            kTopEarlgreyPlicIrqIdGpioGpio8,
            kTopEarlgreyPlicIrqIdGpioGpio9,
            kTopEarlgreyPlicIrqIdGpioGpio10,
            kTopEarlgreyPlicIrqIdGpioGpio11,
            kTopEarlgreyPlicIrqIdGpioGpio12,
            kTopEarlgreyPlicIrqIdGpioGpio13,
            kTopEarlgreyPlicIrqIdGpioGpio14,
            kTopEarlgreyPlicIrqIdGpioGpio15,
            kTopEarlgreyPlicIrqIdGpioGpio16,
            kTopEarlgreyPlicIrqIdGpioGpio17,
            kTopEarlgreyPlicIrqIdGpioGpio18,
            kTopEarlgreyPlicIrqIdGpioGpio19,
            kTopEarlgreyPlicIrqIdGpioGpio20,
            kTopEarlgreyPlicIrqIdGpioGpio21,
            kTopEarlgreyPlicIrqIdGpioGpio22,
            kTopEarlgreyPlicIrqIdGpioGpio23,
            kTopEarlgreyPlicIrqIdGpioGpio24,
            kTopEarlgreyPlicIrqIdGpioGpio25,
            kTopEarlgreyPlicIrqIdGpioGpio26,
            kTopEarlgreyPlicIrqIdGpioGpio27,
            kTopEarlgreyPlicIrqIdGpioGpio28,
            kTopEarlgreyPlicIrqIdGpioGpio29,
            kTopEarlgreyPlicIrqIdGpioGpio30,
            kTopEarlgreyPlicIrqIdGpioGpio31,
        },
    },
};
// Device tables for hmac
_Static_assert(kDtHmacRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtHmacClockCount == 1, "Clock count mismatch");
_Static_assert(kDtHmacIrqTypeCount == 3, "IRQ count mismatch");

typedef struct dt_hmac_info {
  uint32_t base_addrs[kDtHmacRegBlockCount];
  dt_clock_t clocks[kDtHmacClockCount];
  uint32_t irqs[kDtHmacIrqTypeCount];
} dt_hmac_info_t;

static const dt_hmac_info_t dev_table_hmac[kDtDeviceCountHmac] = {
    // Properties for hmac
    {
        .base_addrs = {
            0x41110000,
        },
        .clocks = {
            [kDtHmacClockClk] = kTopEarlgreyClockSrcMain,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdHmacHmacDone,
            kTopEarlgreyPlicIrqIdHmacFifoEmpty,
            kTopEarlgreyPlicIrqIdHmacHmacErr,
        },
    },
};
// Device tables for i2c
_Static_assert(kDtI2cRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtI2cClockCount == 1, "Clock count mismatch");
_Static_assert(kDtI2cIrqTypeCount == 15, "IRQ count mismatch");

typedef struct dt_i2c_info {
  uint32_t base_addrs[kDtI2cRegBlockCount];
  dt_clock_t clocks[kDtI2cClockCount];
  uint32_t irqs[kDtI2cIrqTypeCount];
} dt_i2c_info_t;

static const dt_i2c_info_t dev_table_i2c[kDtDeviceCountI2c] = {
    // Properties for i2c0
    {
        .base_addrs = {
            0x40080000,
        },
        .clocks = {
            [kDtI2cClockClk] = kTopEarlgreyClockSrcIoDiv4,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdI2c0FmtThreshold,
            kTopEarlgreyPlicIrqIdI2c0RxThreshold,
            kTopEarlgreyPlicIrqIdI2c0AcqThreshold,
            kTopEarlgreyPlicIrqIdI2c0RxOverflow,
            kTopEarlgreyPlicIrqIdI2c0Nak,
            kTopEarlgreyPlicIrqIdI2c0SclInterference,
            kTopEarlgreyPlicIrqIdI2c0SdaInterference,
            kTopEarlgreyPlicIrqIdI2c0StretchTimeout,
            kTopEarlgreyPlicIrqIdI2c0SdaUnstable,
            kTopEarlgreyPlicIrqIdI2c0CmdComplete,
            kTopEarlgreyPlicIrqIdI2c0TxStretch,
            kTopEarlgreyPlicIrqIdI2c0TxThreshold,
            kTopEarlgreyPlicIrqIdI2c0AcqFull,
            kTopEarlgreyPlicIrqIdI2c0UnexpStop,
            kTopEarlgreyPlicIrqIdI2c0HostTimeout,
        },
    },
    // Properties for i2c1
    {
        .base_addrs = {
            0x40090000,
        },
        .clocks = {
            [kDtI2cClockClk] = kTopEarlgreyClockSrcIoDiv4,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdI2c1FmtThreshold,
            kTopEarlgreyPlicIrqIdI2c1RxThreshold,
            kTopEarlgreyPlicIrqIdI2c1AcqThreshold,
            kTopEarlgreyPlicIrqIdI2c1RxOverflow,
            kTopEarlgreyPlicIrqIdI2c1Nak,
            kTopEarlgreyPlicIrqIdI2c1SclInterference,
            kTopEarlgreyPlicIrqIdI2c1SdaInterference,
            kTopEarlgreyPlicIrqIdI2c1StretchTimeout,
            kTopEarlgreyPlicIrqIdI2c1SdaUnstable,
            kTopEarlgreyPlicIrqIdI2c1CmdComplete,
            kTopEarlgreyPlicIrqIdI2c1TxStretch,
            kTopEarlgreyPlicIrqIdI2c1TxThreshold,
            kTopEarlgreyPlicIrqIdI2c1AcqFull,
            kTopEarlgreyPlicIrqIdI2c1UnexpStop,
            kTopEarlgreyPlicIrqIdI2c1HostTimeout,
        },
    },
    // Properties for i2c2
    {
        .base_addrs = {
            0x400A0000,
        },
        .clocks = {
            [kDtI2cClockClk] = kTopEarlgreyClockSrcIoDiv4,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdI2c2FmtThreshold,
            kTopEarlgreyPlicIrqIdI2c2RxThreshold,
            kTopEarlgreyPlicIrqIdI2c2AcqThreshold,
            kTopEarlgreyPlicIrqIdI2c2RxOverflow,
            kTopEarlgreyPlicIrqIdI2c2Nak,
            kTopEarlgreyPlicIrqIdI2c2SclInterference,
            kTopEarlgreyPlicIrqIdI2c2SdaInterference,
            kTopEarlgreyPlicIrqIdI2c2StretchTimeout,
            kTopEarlgreyPlicIrqIdI2c2SdaUnstable,
            kTopEarlgreyPlicIrqIdI2c2CmdComplete,
            kTopEarlgreyPlicIrqIdI2c2TxStretch,
            kTopEarlgreyPlicIrqIdI2c2TxThreshold,
            kTopEarlgreyPlicIrqIdI2c2AcqFull,
            kTopEarlgreyPlicIrqIdI2c2UnexpStop,
            kTopEarlgreyPlicIrqIdI2c2HostTimeout,
        },
    },
};
// Device tables for keymgr
_Static_assert(kDtKeymgrRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtKeymgrClockCount == 2, "Clock count mismatch");
_Static_assert(kDtKeymgrIrqTypeCount == 1, "IRQ count mismatch");

typedef struct dt_keymgr_info {
  uint32_t base_addrs[kDtKeymgrRegBlockCount];
  dt_clock_t clocks[kDtKeymgrClockCount];
  uint32_t irqs[kDtKeymgrIrqTypeCount];
} dt_keymgr_info_t;

static const dt_keymgr_info_t dev_table_keymgr[kDtDeviceCountKeymgr] = {
    // Properties for keymgr
    {
        .base_addrs = {
            0x41140000,
        },
        .clocks = {
            [kDtKeymgrClockClk] = kTopEarlgreyClockSrcMain,
            [kDtKeymgrClockEdn] = kTopEarlgreyClockSrcMain,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdKeymgrOpDone,
        },
    },
};
// Device tables for kmac
_Static_assert(kDtKmacRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtKmacClockCount == 2, "Clock count mismatch");
_Static_assert(kDtKmacIrqTypeCount == 3, "IRQ count mismatch");

typedef struct dt_kmac_info {
  uint32_t base_addrs[kDtKmacRegBlockCount];
  dt_clock_t clocks[kDtKmacClockCount];
  uint32_t irqs[kDtKmacIrqTypeCount];
} dt_kmac_info_t;

static const dt_kmac_info_t dev_table_kmac[kDtDeviceCountKmac] = {
    // Properties for kmac
    {
        .base_addrs = {
            0x41120000,
        },
        .clocks = {
            [kDtKmacClockClk] = kTopEarlgreyClockSrcMain,
            [kDtKmacClockEdn] = kTopEarlgreyClockSrcMain,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdKmacKmacDone,
            kTopEarlgreyPlicIrqIdKmacFifoEmpty,
            kTopEarlgreyPlicIrqIdKmacKmacErr,
        },
    },
};
// Device tables for lc_ctrl
_Static_assert(kDtLcCtrlRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtLcCtrlClockCount == 2, "Clock count mismatch");

typedef struct dt_lc_ctrl_info {
  uint32_t base_addrs[kDtLcCtrlRegBlockCount];
  dt_clock_t clocks[kDtLcCtrlClockCount];
} dt_lc_ctrl_info_t;

static const dt_lc_ctrl_info_t dev_table_lc_ctrl[kDtDeviceCountLcCtrl] = {
    // Properties for lc_ctrl
    {
        .base_addrs = {
            0x40140000,
        },
        .clocks = {
            [kDtLcCtrlClockClk] = kTopEarlgreyClockSrcIoDiv4,
            [kDtLcCtrlClockKmac] = kTopEarlgreyClockSrcMain,
        },
    },
};
// Device tables for otbn
_Static_assert(kDtOtbnRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtOtbnClockCount == 3, "Clock count mismatch");
_Static_assert(kDtOtbnIrqTypeCount == 1, "IRQ count mismatch");

typedef struct dt_otbn_info {
  uint32_t base_addrs[kDtOtbnRegBlockCount];
  dt_clock_t clocks[kDtOtbnClockCount];
  uint32_t irqs[kDtOtbnIrqTypeCount];
} dt_otbn_info_t;

static const dt_otbn_info_t dev_table_otbn[kDtDeviceCountOtbn] = {
    // Properties for otbn
    {
        .base_addrs = {
            0x41130000,
        },
        .clocks = {
            [kDtOtbnClockClk] = kTopEarlgreyClockSrcMain,
            [kDtOtbnClockEdn] = kTopEarlgreyClockSrcMain,
            [kDtOtbnClockOtp] = kTopEarlgreyClockSrcIoDiv4,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdOtbnDone,
        },
    },
};
// Device tables for otp_ctrl
_Static_assert(kDtOtpCtrlRegBlockCount == 2, "Reg block count mismatch");
_Static_assert(kDtOtpCtrlClockCount == 2, "Clock count mismatch");
_Static_assert(kDtOtpCtrlIrqTypeCount == 2, "IRQ count mismatch");

typedef struct dt_otp_ctrl_info {
  uint32_t base_addrs[kDtOtpCtrlRegBlockCount];
  dt_clock_t clocks[kDtOtpCtrlClockCount];
  uint32_t irqs[kDtOtpCtrlIrqTypeCount];
} dt_otp_ctrl_info_t;

static const dt_otp_ctrl_info_t dev_table_otp_ctrl[kDtDeviceCountOtpCtrl] = {
    // Properties for otp_ctrl
    {
        .base_addrs = {
            0x40130000,
            0x40138000,
        },
        .clocks = {
            [kDtOtpCtrlClockClk] = kTopEarlgreyClockSrcIoDiv4,
            [kDtOtpCtrlClockEdn] = kTopEarlgreyClockSrcMain,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdOtpCtrlOtpOperationDone,
            kTopEarlgreyPlicIrqIdOtpCtrlOtpError,
        },
    },
};
// Device tables for pattgen
_Static_assert(kDtPattgenRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtPattgenClockCount == 1, "Clock count mismatch");
_Static_assert(kDtPattgenIrqTypeCount == 2, "IRQ count mismatch");

typedef struct dt_pattgen_info {
  uint32_t base_addrs[kDtPattgenRegBlockCount];
  dt_clock_t clocks[kDtPattgenClockCount];
  uint32_t irqs[kDtPattgenIrqTypeCount];
} dt_pattgen_info_t;

static const dt_pattgen_info_t dev_table_pattgen[kDtDeviceCountPattgen] = {
    // Properties for pattgen
    {
        .base_addrs = {
            0x400E0000,
        },
        .clocks = {
            [kDtPattgenClockClk] = kTopEarlgreyClockSrcIoDiv4,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdPattgenDoneCh0,
            kTopEarlgreyPlicIrqIdPattgenDoneCh1,
        },
    },
};
// Device tables for pinmux
_Static_assert(kDtPinmuxRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtPinmuxClockCount == 2, "Clock count mismatch");

typedef struct dt_pinmux_info {
  uint32_t base_addrs[kDtPinmuxRegBlockCount];
  dt_clock_t clocks[kDtPinmuxClockCount];
} dt_pinmux_info_t;

static const dt_pinmux_info_t dev_table_pinmux[kDtDeviceCountPinmux] = {
    // Properties for pinmux_aon
    {
        .base_addrs = {
            0x40460000,
        },
        .clocks = {
            [kDtPinmuxClockClk] = kTopEarlgreyClockSrcIoDiv4,
            [kDtPinmuxClockAon] = kTopEarlgreyClockSrcAon,
        },
    },
};
// Device tables for pwm
_Static_assert(kDtPwmRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtPwmClockCount == 2, "Clock count mismatch");

typedef struct dt_pwm_info {
  uint32_t base_addrs[kDtPwmRegBlockCount];
  dt_clock_t clocks[kDtPwmClockCount];
} dt_pwm_info_t;

static const dt_pwm_info_t dev_table_pwm[kDtDeviceCountPwm] = {
    // Properties for pwm_aon
    {
        .base_addrs = {
            0x40450000,
        },
        .clocks = {
            [kDtPwmClockClk] = kTopEarlgreyClockSrcIoDiv4,
            [kDtPwmClockCore] = kTopEarlgreyClockSrcAon,
        },
    },
};
// Device tables for pwrmgr
_Static_assert(kDtPwrmgrRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtPwrmgrClockCount == 4, "Clock count mismatch");
_Static_assert(kDtPwrmgrIrqTypeCount == 1, "IRQ count mismatch");

typedef struct dt_pwrmgr_info {
  uint32_t base_addrs[kDtPwrmgrRegBlockCount];
  dt_clock_t clocks[kDtPwrmgrClockCount];
  uint32_t irqs[kDtPwrmgrIrqTypeCount];
} dt_pwrmgr_info_t;

static const dt_pwrmgr_info_t dev_table_pwrmgr[kDtDeviceCountPwrmgr] = {
    // Properties for pwrmgr_aon
    {
        .base_addrs = {
            0x40400000,
        },
        .clocks = {
            [kDtPwrmgrClockClk] = kTopEarlgreyClockSrcIoDiv4,
            [kDtPwrmgrClockSlow] = kTopEarlgreyClockSrcAon,
            [kDtPwrmgrClockLc] = kTopEarlgreyClockSrcIoDiv4,
            [kDtPwrmgrClockEsc] = kTopEarlgreyClockSrcIoDiv4,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
        },
    },
};
// Device tables for rom_ctrl
_Static_assert(kDtRomCtrlRegBlockCount == 2, "Reg block count mismatch");
_Static_assert(kDtRomCtrlClockCount == 1, "Clock count mismatch");

typedef struct dt_rom_ctrl_info {
  uint32_t base_addrs[kDtRomCtrlRegBlockCount];
  dt_clock_t clocks[kDtRomCtrlClockCount];
} dt_rom_ctrl_info_t;

static const dt_rom_ctrl_info_t dev_table_rom_ctrl[kDtDeviceCountRomCtrl] = {
    // Properties for rom_ctrl
    {
        .base_addrs = {
            0x00008000,
            0x411e0000,
        },
        .clocks = {
            [kDtRomCtrlClockClk] = kTopEarlgreyClockSrcMain,
        },
    },
};
// Device tables for rstmgr
_Static_assert(kDtRstmgrRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtRstmgrClockCount == 8, "Clock count mismatch");

typedef struct dt_rstmgr_info {
  uint32_t base_addrs[kDtRstmgrRegBlockCount];
  dt_clock_t clocks[kDtRstmgrClockCount];
} dt_rstmgr_info_t;

static const dt_rstmgr_info_t dev_table_rstmgr[kDtDeviceCountRstmgr] = {
    // Properties for rstmgr_aon
    {
        .base_addrs = {
            0x40410000,
        },
        .clocks = {
            [kDtRstmgrClockClk] = kTopEarlgreyClockSrcIoDiv4,
            [kDtRstmgrClockPor] = kTopEarlgreyClockSrcIoDiv4,
            [kDtRstmgrClockAon] = kTopEarlgreyClockSrcAon,
            [kDtRstmgrClockMain] = kTopEarlgreyClockSrcMain,
            [kDtRstmgrClockIo] = kTopEarlgreyClockSrcIo,
            [kDtRstmgrClockUsb] = kTopEarlgreyClockSrcUsb,
            [kDtRstmgrClockIoDiv2] = kTopEarlgreyClockSrcIoDiv2,
            [kDtRstmgrClockIoDiv4] = kTopEarlgreyClockSrcIoDiv4,
        },
    },
};
// Device tables for rv_core_ibex
_Static_assert(kDtRvCoreIbexRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtRvCoreIbexClockCount == 4, "Clock count mismatch");

typedef struct dt_rv_core_ibex_info {
  uint32_t base_addrs[kDtRvCoreIbexRegBlockCount];
  dt_clock_t clocks[kDtRvCoreIbexClockCount];
} dt_rv_core_ibex_info_t;

static const dt_rv_core_ibex_info_t dev_table_rv_core_ibex[kDtDeviceCountRvCoreIbex] = {
    // Properties for rv_core_ibex
    {
        .base_addrs = {
            0x411F0000,
        },
        .clocks = {
            [kDtRvCoreIbexClockClk] = kTopEarlgreyClockSrcMain,
            [kDtRvCoreIbexClockEdn] = kTopEarlgreyClockSrcMain,
            [kDtRvCoreIbexClockEsc] = kTopEarlgreyClockSrcIoDiv4,
            [kDtRvCoreIbexClockOtp] = kTopEarlgreyClockSrcIoDiv4,
        },
    },
};
// Device tables for rv_dm
_Static_assert(kDtRvDmRegBlockCount == 2, "Reg block count mismatch");
_Static_assert(kDtRvDmClockCount == 1, "Clock count mismatch");

typedef struct dt_rv_dm_info {
  uint32_t base_addrs[kDtRvDmRegBlockCount];
  dt_clock_t clocks[kDtRvDmClockCount];
} dt_rv_dm_info_t;

static const dt_rv_dm_info_t dev_table_rv_dm[kDtDeviceCountRvDm] = {
    // Properties for rv_dm
    {
        .base_addrs = {
            0x00010000,
            0x41200000,
        },
        .clocks = {
            [kDtRvDmClockClk] = kTopEarlgreyClockSrcMain,
        },
    },
};
// Device tables for rv_plic
_Static_assert(kDtRvPlicRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtRvPlicClockCount == 1, "Clock count mismatch");

typedef struct dt_rv_plic_info {
  uint32_t base_addrs[kDtRvPlicRegBlockCount];
  dt_clock_t clocks[kDtRvPlicClockCount];
} dt_rv_plic_info_t;

static const dt_rv_plic_info_t dev_table_rv_plic[kDtDeviceCountRvPlic] = {
    // Properties for rv_plic
    {
        .base_addrs = {
            0x48000000,
        },
        .clocks = {
            [kDtRvPlicClockClk] = kTopEarlgreyClockSrcMain,
        },
    },
};
// Device tables for rv_timer
_Static_assert(kDtRvTimerRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtRvTimerClockCount == 1, "Clock count mismatch");
_Static_assert(kDtRvTimerIrqTypeCount == 1, "IRQ count mismatch");

typedef struct dt_rv_timer_info {
  uint32_t base_addrs[kDtRvTimerRegBlockCount];
  dt_clock_t clocks[kDtRvTimerClockCount];
  uint32_t irqs[kDtRvTimerIrqTypeCount];
} dt_rv_timer_info_t;

static const dt_rv_timer_info_t dev_table_rv_timer[kDtDeviceCountRvTimer] = {
    // Properties for rv_timer
    {
        .base_addrs = {
            0x40100000,
        },
        .clocks = {
            [kDtRvTimerClockClk] = kTopEarlgreyClockSrcIoDiv4,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdRvTimerTimerExpiredHart0Timer0,
        },
    },
};
// Device tables for sensor_ctrl
// TODO: Handle tables for top_reggen types
// Device tables for spi_device
_Static_assert(kDtSpiDeviceRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtSpiDeviceClockCount == 1, "Clock count mismatch");
_Static_assert(kDtSpiDeviceIrqTypeCount == 8, "IRQ count mismatch");

typedef struct dt_spi_device_info {
  uint32_t base_addrs[kDtSpiDeviceRegBlockCount];
  dt_clock_t clocks[kDtSpiDeviceClockCount];
  uint32_t irqs[kDtSpiDeviceIrqTypeCount];
} dt_spi_device_info_t;

static const dt_spi_device_info_t dev_table_spi_device[kDtDeviceCountSpiDevice] = {
    // Properties for spi_device
    {
        .base_addrs = {
            0x40050000,
        },
        .clocks = {
            [kDtSpiDeviceClockClk] = kTopEarlgreyClockSrcIoDiv4,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty,
            kTopEarlgreyPlicIrqIdSpiDeviceUploadPayloadNotEmpty,
            kTopEarlgreyPlicIrqIdSpiDeviceUploadPayloadOverflow,
            kTopEarlgreyPlicIrqIdSpiDeviceReadbufWatermark,
            kTopEarlgreyPlicIrqIdSpiDeviceReadbufFlip,
            kTopEarlgreyPlicIrqIdSpiDeviceTpmHeaderNotEmpty,
            kTopEarlgreyPlicIrqIdSpiDeviceTpmRdfifoCmdEnd,
            kTopEarlgreyPlicIrqIdSpiDeviceTpmRdfifoDrop,
        },
    },
};
// Device tables for spi_host
_Static_assert(kDtSpiHostRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtSpiHostClockCount == 1, "Clock count mismatch");
_Static_assert(kDtSpiHostIrqTypeCount == 2, "IRQ count mismatch");

typedef struct dt_spi_host_info {
  uint32_t base_addrs[kDtSpiHostRegBlockCount];
  dt_clock_t clocks[kDtSpiHostClockCount];
  uint32_t irqs[kDtSpiHostIrqTypeCount];
} dt_spi_host_info_t;

static const dt_spi_host_info_t dev_table_spi_host[kDtDeviceCountSpiHost] = {
    // Properties for spi_host0
    {
        .base_addrs = {
            0x40300000,
        },
        .clocks = {
            [kDtSpiHostClockClk] = kTopEarlgreyClockSrcIo,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdSpiHost0Error,
            kTopEarlgreyPlicIrqIdSpiHost0SpiEvent,
        },
    },
    // Properties for spi_host1
    {
        .base_addrs = {
            0x40310000,
        },
        .clocks = {
            [kDtSpiHostClockClk] = kTopEarlgreyClockSrcIoDiv2,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdSpiHost1Error,
            kTopEarlgreyPlicIrqIdSpiHost1SpiEvent,
        },
    },
};
// Device tables for sram_ctrl
_Static_assert(kDtSramCtrlRegBlockCount == 2, "Reg block count mismatch");
_Static_assert(kDtSramCtrlClockCount == 2, "Clock count mismatch");

typedef struct dt_sram_ctrl_info {
  uint32_t base_addrs[kDtSramCtrlRegBlockCount];
  dt_clock_t clocks[kDtSramCtrlClockCount];
} dt_sram_ctrl_info_t;

static const dt_sram_ctrl_info_t dev_table_sram_ctrl[kDtDeviceCountSramCtrl] = {
    // Properties for sram_ctrl_ret_aon
    {
        .base_addrs = {
            0x40500000,
            0x40600000,
        },
        .clocks = {
            [kDtSramCtrlClockClk] = kTopEarlgreyClockSrcIoDiv4,
            [kDtSramCtrlClockOtp] = kTopEarlgreyClockSrcIoDiv4,
        },
    },
    // Properties for sram_ctrl_main
    {
        .base_addrs = {
            0x411C0000,
            0x10000000,
        },
        .clocks = {
            [kDtSramCtrlClockClk] = kTopEarlgreyClockSrcMain,
            [kDtSramCtrlClockOtp] = kTopEarlgreyClockSrcIoDiv4,
        },
    },
};
// Device tables for sysrst_ctrl
_Static_assert(kDtSysrstCtrlRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtSysrstCtrlClockCount == 2, "Clock count mismatch");
_Static_assert(kDtSysrstCtrlIrqTypeCount == 1, "IRQ count mismatch");

typedef struct dt_sysrst_ctrl_info {
  uint32_t base_addrs[kDtSysrstCtrlRegBlockCount];
  dt_clock_t clocks[kDtSysrstCtrlClockCount];
  uint32_t irqs[kDtSysrstCtrlIrqTypeCount];
} dt_sysrst_ctrl_info_t;

static const dt_sysrst_ctrl_info_t dev_table_sysrst_ctrl[kDtDeviceCountSysrstCtrl] = {
    // Properties for sysrst_ctrl_aon
    {
        .base_addrs = {
            0x40430000,
        },
        .clocks = {
            [kDtSysrstCtrlClockClk] = kTopEarlgreyClockSrcIoDiv4,
            [kDtSysrstCtrlClockAon] = kTopEarlgreyClockSrcAon,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdSysrstCtrlAonEventDetected,
        },
    },
};
// Device tables for uart
_Static_assert(kDtUartRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtUartClockCount == 1, "Clock count mismatch");
_Static_assert(kDtUartIrqTypeCount == 8, "IRQ count mismatch");

typedef struct dt_uart_info {
  uint32_t base_addrs[kDtUartRegBlockCount];
  dt_clock_t clocks[kDtUartClockCount];
  uint32_t irqs[kDtUartIrqTypeCount];
} dt_uart_info_t;

static const dt_uart_info_t dev_table_uart[kDtDeviceCountUart] = {
    // Properties for uart0
    {
        .base_addrs = {
            0x40000000,
        },
        .clocks = {
            [kDtUartClockClk] = kTopEarlgreyClockSrcIoDiv4,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdUart0TxWatermark,
            kTopEarlgreyPlicIrqIdUart0RxWatermark,
            kTopEarlgreyPlicIrqIdUart0TxEmpty,
            kTopEarlgreyPlicIrqIdUart0RxOverflow,
            kTopEarlgreyPlicIrqIdUart0RxFrameErr,
            kTopEarlgreyPlicIrqIdUart0RxBreakErr,
            kTopEarlgreyPlicIrqIdUart0RxTimeout,
            kTopEarlgreyPlicIrqIdUart0RxParityErr,
        },
    },
    // Properties for uart1
    {
        .base_addrs = {
            0x40010000,
        },
        .clocks = {
            [kDtUartClockClk] = kTopEarlgreyClockSrcIoDiv4,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdUart1TxWatermark,
            kTopEarlgreyPlicIrqIdUart1RxWatermark,
            kTopEarlgreyPlicIrqIdUart1TxEmpty,
            kTopEarlgreyPlicIrqIdUart1RxOverflow,
            kTopEarlgreyPlicIrqIdUart1RxFrameErr,
            kTopEarlgreyPlicIrqIdUart1RxBreakErr,
            kTopEarlgreyPlicIrqIdUart1RxTimeout,
            kTopEarlgreyPlicIrqIdUart1RxParityErr,
        },
    },
    // Properties for uart2
    {
        .base_addrs = {
            0x40020000,
        },
        .clocks = {
            [kDtUartClockClk] = kTopEarlgreyClockSrcIoDiv4,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdUart2TxWatermark,
            kTopEarlgreyPlicIrqIdUart2RxWatermark,
            kTopEarlgreyPlicIrqIdUart2TxEmpty,
            kTopEarlgreyPlicIrqIdUart2RxOverflow,
            kTopEarlgreyPlicIrqIdUart2RxFrameErr,
            kTopEarlgreyPlicIrqIdUart2RxBreakErr,
            kTopEarlgreyPlicIrqIdUart2RxTimeout,
            kTopEarlgreyPlicIrqIdUart2RxParityErr,
        },
    },
    // Properties for uart3
    {
        .base_addrs = {
            0x40030000,
        },
        .clocks = {
            [kDtUartClockClk] = kTopEarlgreyClockSrcIoDiv4,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdUart3TxWatermark,
            kTopEarlgreyPlicIrqIdUart3RxWatermark,
            kTopEarlgreyPlicIrqIdUart3TxEmpty,
            kTopEarlgreyPlicIrqIdUart3RxOverflow,
            kTopEarlgreyPlicIrqIdUart3RxFrameErr,
            kTopEarlgreyPlicIrqIdUart3RxBreakErr,
            kTopEarlgreyPlicIrqIdUart3RxTimeout,
            kTopEarlgreyPlicIrqIdUart3RxParityErr,
        },
    },
};
// Device tables for usbdev
_Static_assert(kDtUsbdevRegBlockCount == 1, "Reg block count mismatch");
_Static_assert(kDtUsbdevClockCount == 2, "Clock count mismatch");
_Static_assert(kDtUsbdevIrqTypeCount == 18, "IRQ count mismatch");

typedef struct dt_usbdev_info {
  uint32_t base_addrs[kDtUsbdevRegBlockCount];
  dt_clock_t clocks[kDtUsbdevClockCount];
  uint32_t irqs[kDtUsbdevIrqTypeCount];
} dt_usbdev_info_t;

static const dt_usbdev_info_t dev_table_usbdev[kDtDeviceCountUsbdev] = {
    // Properties for usbdev
    {
        .base_addrs = {
            0x40320000,
        },
        .clocks = {
            [kDtUsbdevClockClk] = kTopEarlgreyClockSrcUsb,
            [kDtUsbdevClockAon] = kTopEarlgreyClockSrcAon,
        },
        .irqs = {
            kTopEarlgreyPlicIrqIdUsbdevPktReceived,
            kTopEarlgreyPlicIrqIdUsbdevPktSent,
            kTopEarlgreyPlicIrqIdUsbdevDisconnected,
            kTopEarlgreyPlicIrqIdUsbdevHostLost,
            kTopEarlgreyPlicIrqIdUsbdevLinkReset,
            kTopEarlgreyPlicIrqIdUsbdevLinkSuspend,
            kTopEarlgreyPlicIrqIdUsbdevLinkResume,
            kTopEarlgreyPlicIrqIdUsbdevAvOutEmpty,
            kTopEarlgreyPlicIrqIdUsbdevRxFull,
            kTopEarlgreyPlicIrqIdUsbdevAvOverflow,
            kTopEarlgreyPlicIrqIdUsbdevLinkInErr,
            kTopEarlgreyPlicIrqIdUsbdevRxCrcErr,
            kTopEarlgreyPlicIrqIdUsbdevRxPidErr,
            kTopEarlgreyPlicIrqIdUsbdevRxBitstuffErr,
            kTopEarlgreyPlicIrqIdUsbdevFrame,
            kTopEarlgreyPlicIrqIdUsbdevPowered,
            kTopEarlgreyPlicIrqIdUsbdevLinkOutErr,
            kTopEarlgreyPlicIrqIdUsbdevAvSetupEmpty,
        },
    },
};


/**
 * A set of tables containing top-level device info. The tables represent a
 * flattened tree of tables that group info by device type. A given device's
 * associated info is located at the base index for that device type's table,
 * plus the number of such devices that were in the top-level hjson file before
 * the given device.
 */
typedef struct top_device_table {
  uint32_t dev_type_base[kDtDeviceTypeCount];
  uint32_t dev_type_len[kDtDeviceTypeCount];
  dt_device_type_t device_type[kDtDeviceIdCount];
} top_device_table_t;

static const top_device_table_t devices = {
    .dev_type_base = {
        [kDtDeviceTypeUnknown] = kDtDeviceIdBaseUnknown,
        [kDtDeviceTypeUart] = kDtDeviceIdBaseUart,
        [kDtDeviceTypeGpio] = kDtDeviceIdBaseGpio,
        [kDtDeviceTypeSpiDevice] = kDtDeviceIdBaseSpiDevice,
        [kDtDeviceTypeI2c] = kDtDeviceIdBaseI2c,
        [kDtDeviceTypePattgen] = kDtDeviceIdBasePattgen,
        [kDtDeviceTypeRvTimer] = kDtDeviceIdBaseRvTimer,
        [kDtDeviceTypeOtpCtrl] = kDtDeviceIdBaseOtpCtrl,
        [kDtDeviceTypeLcCtrl] = kDtDeviceIdBaseLcCtrl,
        [kDtDeviceTypeAlertHandler] = kDtDeviceIdBaseAlertHandler,
        [kDtDeviceTypeSpiHost] = kDtDeviceIdBaseSpiHost,
        [kDtDeviceTypeUsbdev] = kDtDeviceIdBaseUsbdev,
        [kDtDeviceTypePwrmgr] = kDtDeviceIdBasePwrmgr,
        [kDtDeviceTypeRstmgr] = kDtDeviceIdBaseRstmgr,
        [kDtDeviceTypeClkmgr] = kDtDeviceIdBaseClkmgr,
        [kDtDeviceTypeSysrstCtrl] = kDtDeviceIdBaseSysrstCtrl,
        [kDtDeviceTypeAdcCtrl] = kDtDeviceIdBaseAdcCtrl,
        [kDtDeviceTypePwm] = kDtDeviceIdBasePwm,
        [kDtDeviceTypePinmux] = kDtDeviceIdBasePinmux,
        [kDtDeviceTypeAonTimer] = kDtDeviceIdBaseAonTimer,
        [kDtDeviceTypeAst] = kDtDeviceIdBaseAst,
        [kDtDeviceTypeSensorCtrl] = kDtDeviceIdBaseSensorCtrl,
        [kDtDeviceTypeSramCtrl] = kDtDeviceIdBaseSramCtrl,
        [kDtDeviceTypeFlashCtrl] = kDtDeviceIdBaseFlashCtrl,
        [kDtDeviceTypeRvDm] = kDtDeviceIdBaseRvDm,
        [kDtDeviceTypeRvPlic] = kDtDeviceIdBaseRvPlic,
        [kDtDeviceTypeAes] = kDtDeviceIdBaseAes,
        [kDtDeviceTypeHmac] = kDtDeviceIdBaseHmac,
        [kDtDeviceTypeKmac] = kDtDeviceIdBaseKmac,
        [kDtDeviceTypeOtbn] = kDtDeviceIdBaseOtbn,
        [kDtDeviceTypeKeymgr] = kDtDeviceIdBaseKeymgr,
        [kDtDeviceTypeCsrng] = kDtDeviceIdBaseCsrng,
        [kDtDeviceTypeEntropySrc] = kDtDeviceIdBaseEntropySrc,
        [kDtDeviceTypeEdn] = kDtDeviceIdBaseEdn,
        [kDtDeviceTypeRomCtrl] = kDtDeviceIdBaseRomCtrl,
        [kDtDeviceTypeRvCoreIbex] = kDtDeviceIdBaseRvCoreIbex,
    },
    .dev_type_len = {
        [kDtDeviceTypeUnknown] = kDtDeviceCountUnknown,
        [kDtDeviceTypeUart] = kDtDeviceCountUart,
        [kDtDeviceTypeGpio] = kDtDeviceCountGpio,
        [kDtDeviceTypeSpiDevice] = kDtDeviceCountSpiDevice,
        [kDtDeviceTypeI2c] = kDtDeviceCountI2c,
        [kDtDeviceTypePattgen] = kDtDeviceCountPattgen,
        [kDtDeviceTypeRvTimer] = kDtDeviceCountRvTimer,
        [kDtDeviceTypeOtpCtrl] = kDtDeviceCountOtpCtrl,
        [kDtDeviceTypeLcCtrl] = kDtDeviceCountLcCtrl,
        [kDtDeviceTypeAlertHandler] = kDtDeviceCountAlertHandler,
        [kDtDeviceTypeSpiHost] = kDtDeviceCountSpiHost,
        [kDtDeviceTypeUsbdev] = kDtDeviceCountUsbdev,
        [kDtDeviceTypePwrmgr] = kDtDeviceCountPwrmgr,
        [kDtDeviceTypeRstmgr] = kDtDeviceCountRstmgr,
        [kDtDeviceTypeClkmgr] = kDtDeviceCountClkmgr,
        [kDtDeviceTypeSysrstCtrl] = kDtDeviceCountSysrstCtrl,
        [kDtDeviceTypeAdcCtrl] = kDtDeviceCountAdcCtrl,
        [kDtDeviceTypePwm] = kDtDeviceCountPwm,
        [kDtDeviceTypePinmux] = kDtDeviceCountPinmux,
        [kDtDeviceTypeAonTimer] = kDtDeviceCountAonTimer,
        [kDtDeviceTypeAst] = kDtDeviceCountAst,
        [kDtDeviceTypeSensorCtrl] = kDtDeviceCountSensorCtrl,
        [kDtDeviceTypeSramCtrl] = kDtDeviceCountSramCtrl,
        [kDtDeviceTypeFlashCtrl] = kDtDeviceCountFlashCtrl,
        [kDtDeviceTypeRvDm] = kDtDeviceCountRvDm,
        [kDtDeviceTypeRvPlic] = kDtDeviceCountRvPlic,
        [kDtDeviceTypeAes] = kDtDeviceCountAes,
        [kDtDeviceTypeHmac] = kDtDeviceCountHmac,
        [kDtDeviceTypeKmac] = kDtDeviceCountKmac,
        [kDtDeviceTypeOtbn] = kDtDeviceCountOtbn,
        [kDtDeviceTypeKeymgr] = kDtDeviceCountKeymgr,
        [kDtDeviceTypeCsrng] = kDtDeviceCountCsrng,
        [kDtDeviceTypeEntropySrc] = kDtDeviceCountEntropySrc,
        [kDtDeviceTypeEdn] = kDtDeviceCountEdn,
        [kDtDeviceTypeRomCtrl] = kDtDeviceCountRomCtrl,
        [kDtDeviceTypeRvCoreIbex] = kDtDeviceCountRvCoreIbex,
    },
    .device_type = {
        [kDtDeviceIdUart0] = kDtDeviceTypeUart,
        [kDtDeviceIdUart1] = kDtDeviceTypeUart,
        [kDtDeviceIdUart2] = kDtDeviceTypeUart,
        [kDtDeviceIdUart3] = kDtDeviceTypeUart,
        [kDtDeviceIdGpio] = kDtDeviceTypeGpio,
        [kDtDeviceIdSpiDevice] = kDtDeviceTypeSpiDevice,
        [kDtDeviceIdI2c0] = kDtDeviceTypeI2c,
        [kDtDeviceIdI2c1] = kDtDeviceTypeI2c,
        [kDtDeviceIdI2c2] = kDtDeviceTypeI2c,
        [kDtDeviceIdPattgen] = kDtDeviceTypePattgen,
        [kDtDeviceIdRvTimer] = kDtDeviceTypeRvTimer,
        [kDtDeviceIdOtpCtrl] = kDtDeviceTypeOtpCtrl,
        [kDtDeviceIdLcCtrl] = kDtDeviceTypeLcCtrl,
        [kDtDeviceIdAlertHandler] = kDtDeviceTypeAlertHandler,
        [kDtDeviceIdSpiHost0] = kDtDeviceTypeSpiHost,
        [kDtDeviceIdSpiHost1] = kDtDeviceTypeSpiHost,
        [kDtDeviceIdUsbdev] = kDtDeviceTypeUsbdev,
        [kDtDeviceIdPwrmgrAon] = kDtDeviceTypePwrmgr,
        [kDtDeviceIdRstmgrAon] = kDtDeviceTypeRstmgr,
        [kDtDeviceIdClkmgrAon] = kDtDeviceTypeClkmgr,
        [kDtDeviceIdSysrstCtrlAon] = kDtDeviceTypeSysrstCtrl,
        [kDtDeviceIdAdcCtrlAon] = kDtDeviceTypeAdcCtrl,
        [kDtDeviceIdPwmAon] = kDtDeviceTypePwm,
        [kDtDeviceIdPinmuxAon] = kDtDeviceTypePinmux,
        [kDtDeviceIdAonTimerAon] = kDtDeviceTypeAonTimer,
        [kDtDeviceIdAst] = kDtDeviceTypeAst,
        [kDtDeviceIdSensorCtrlAon] = kDtDeviceTypeSensorCtrl,
        [kDtDeviceIdSramCtrlRetAon] = kDtDeviceTypeSramCtrl,
        [kDtDeviceIdSramCtrlMain] = kDtDeviceTypeSramCtrl,
        [kDtDeviceIdFlashCtrl] = kDtDeviceTypeFlashCtrl,
        [kDtDeviceIdRvDm] = kDtDeviceTypeRvDm,
        [kDtDeviceIdRvPlic] = kDtDeviceTypeRvPlic,
        [kDtDeviceIdAes] = kDtDeviceTypeAes,
        [kDtDeviceIdHmac] = kDtDeviceTypeHmac,
        [kDtDeviceIdKmac] = kDtDeviceTypeKmac,
        [kDtDeviceIdOtbn] = kDtDeviceTypeOtbn,
        [kDtDeviceIdKeymgr] = kDtDeviceTypeKeymgr,
        [kDtDeviceIdCsrng] = kDtDeviceTypeCsrng,
        [kDtDeviceIdEntropySrc] = kDtDeviceTypeEntropySrc,
        [kDtDeviceIdEdn0] = kDtDeviceTypeEdn,
        [kDtDeviceIdEdn1] = kDtDeviceTypeEdn,
        [kDtDeviceIdRomCtrl] = kDtDeviceTypeRomCtrl,
        [kDtDeviceIdRvCoreIbex] = kDtDeviceTypeRvCoreIbex,
    },
};

uint32_t dt_num_devices(dt_device_type_t dev_type) {
  if (dev_type < kDtDeviceTypeCount) {
    return devices.dev_type_len[dev_type];
  }
  return 0;
}

dt_device_t dt_get_device(dt_device_type_t dev_type, uint16_t dev_idx) {
  if (dev_type < kDtDeviceTypeCount) {
    if (dev_idx < devices.dev_type_len[dev_type]) {
      return devices.dev_type_base[dev_type] + dev_idx;
    }
  }
  return kDtDeviceUnknown;
}

inline dt_device_type_t __dt_device_get_type(dt_device_t dev) {
  dt_device_type_t dev_type = kDtDeviceTypeUnknown;
  if (dev < kDtDeviceIdCount) {
    switch (dev) {
      case kDtDeviceIdUart0:
        dev_type = kDtDeviceTypeUart;
        break;
      case kDtDeviceIdUart1:
        dev_type = kDtDeviceTypeUart;
        break;
      case kDtDeviceIdUart2:
        dev_type = kDtDeviceTypeUart;
        break;
      case kDtDeviceIdUart3:
        dev_type = kDtDeviceTypeUart;
        break;
      case kDtDeviceIdGpio:
        dev_type = kDtDeviceTypeGpio;
        break;
      case kDtDeviceIdSpiDevice:
        dev_type = kDtDeviceTypeSpiDevice;
        break;
      case kDtDeviceIdI2c0:
        dev_type = kDtDeviceTypeI2c;
        break;
      case kDtDeviceIdI2c1:
        dev_type = kDtDeviceTypeI2c;
        break;
      case kDtDeviceIdI2c2:
        dev_type = kDtDeviceTypeI2c;
        break;
      case kDtDeviceIdPattgen:
        dev_type = kDtDeviceTypePattgen;
        break;
      case kDtDeviceIdRvTimer:
        dev_type = kDtDeviceTypeRvTimer;
        break;
      case kDtDeviceIdOtpCtrl:
        dev_type = kDtDeviceTypeOtpCtrl;
        break;
      case kDtDeviceIdLcCtrl:
        dev_type = kDtDeviceTypeLcCtrl;
        break;
      case kDtDeviceIdAlertHandler:
        dev_type = kDtDeviceTypeAlertHandler;
        break;
      case kDtDeviceIdSpiHost0:
        dev_type = kDtDeviceTypeSpiHost;
        break;
      case kDtDeviceIdSpiHost1:
        dev_type = kDtDeviceTypeSpiHost;
        break;
      case kDtDeviceIdUsbdev:
        dev_type = kDtDeviceTypeUsbdev;
        break;
      case kDtDeviceIdPwrmgrAon:
        dev_type = kDtDeviceTypePwrmgr;
        break;
      case kDtDeviceIdRstmgrAon:
        dev_type = kDtDeviceTypeRstmgr;
        break;
      case kDtDeviceIdClkmgrAon:
        dev_type = kDtDeviceTypeClkmgr;
        break;
      case kDtDeviceIdSysrstCtrlAon:
        dev_type = kDtDeviceTypeSysrstCtrl;
        break;
      case kDtDeviceIdAdcCtrlAon:
        dev_type = kDtDeviceTypeAdcCtrl;
        break;
      case kDtDeviceIdPwmAon:
        dev_type = kDtDeviceTypePwm;
        break;
      case kDtDeviceIdPinmuxAon:
        dev_type = kDtDeviceTypePinmux;
        break;
      case kDtDeviceIdAonTimerAon:
        dev_type = kDtDeviceTypeAonTimer;
        break;
      case kDtDeviceIdAst:
        dev_type = kDtDeviceTypeAst;
        break;
      case kDtDeviceIdSensorCtrlAon:
        dev_type = kDtDeviceTypeSensorCtrl;
        break;
      case kDtDeviceIdSramCtrlRetAon:
        dev_type = kDtDeviceTypeSramCtrl;
        break;
      case kDtDeviceIdSramCtrlMain:
        dev_type = kDtDeviceTypeSramCtrl;
        break;
      case kDtDeviceIdFlashCtrl:
        dev_type = kDtDeviceTypeFlashCtrl;
        break;
      case kDtDeviceIdRvDm:
        dev_type = kDtDeviceTypeRvDm;
        break;
      case kDtDeviceIdRvPlic:
        dev_type = kDtDeviceTypeRvPlic;
        break;
      case kDtDeviceIdAes:
        dev_type = kDtDeviceTypeAes;
        break;
      case kDtDeviceIdHmac:
        dev_type = kDtDeviceTypeHmac;
        break;
      case kDtDeviceIdKmac:
        dev_type = kDtDeviceTypeKmac;
        break;
      case kDtDeviceIdOtbn:
        dev_type = kDtDeviceTypeOtbn;
        break;
      case kDtDeviceIdKeymgr:
        dev_type = kDtDeviceTypeKeymgr;
        break;
      case kDtDeviceIdCsrng:
        dev_type = kDtDeviceTypeCsrng;
        break;
      case kDtDeviceIdEntropySrc:
        dev_type = kDtDeviceTypeEntropySrc;
        break;
      case kDtDeviceIdEdn0:
        dev_type = kDtDeviceTypeEdn;
        break;
      case kDtDeviceIdEdn1:
        dev_type = kDtDeviceTypeEdn;
        break;
      case kDtDeviceIdRomCtrl:
        dev_type = kDtDeviceTypeRomCtrl;
        break;
      case kDtDeviceIdRvCoreIbex:
        dev_type = kDtDeviceTypeRvCoreIbex;
        break;
      default:
        break;
    }
  }
  return dev_type;
}

inline uint32_t __dt_device_get_index(dt_device_t dev) {
  if (dev < kDtDeviceIdCount) {
    switch (dev) {
      case kDtDeviceIdUart0:
        return 0;
      case kDtDeviceIdUart1:
        return 1;
      case kDtDeviceIdUart2:
        return 2;
      case kDtDeviceIdUart3:
        return 3;
      case kDtDeviceIdGpio:
        return 0;
      case kDtDeviceIdSpiDevice:
        return 0;
      case kDtDeviceIdI2c0:
        return 0;
      case kDtDeviceIdI2c1:
        return 1;
      case kDtDeviceIdI2c2:
        return 2;
      case kDtDeviceIdPattgen:
        return 0;
      case kDtDeviceIdRvTimer:
        return 0;
      case kDtDeviceIdOtpCtrl:
        return 0;
      case kDtDeviceIdLcCtrl:
        return 0;
      case kDtDeviceIdAlertHandler:
        return 0;
      case kDtDeviceIdSpiHost0:
        return 0;
      case kDtDeviceIdSpiHost1:
        return 1;
      case kDtDeviceIdUsbdev:
        return 0;
      case kDtDeviceIdPwrmgrAon:
        return 0;
      case kDtDeviceIdRstmgrAon:
        return 0;
      case kDtDeviceIdClkmgrAon:
        return 0;
      case kDtDeviceIdSysrstCtrlAon:
        return 0;
      case kDtDeviceIdAdcCtrlAon:
        return 0;
      case kDtDeviceIdPwmAon:
        return 0;
      case kDtDeviceIdPinmuxAon:
        return 0;
      case kDtDeviceIdAonTimerAon:
        return 0;
      case kDtDeviceIdAst:
        return 0;
      case kDtDeviceIdSensorCtrlAon:
        return 0;
      case kDtDeviceIdSramCtrlRetAon:
        return 0;
      case kDtDeviceIdSramCtrlMain:
        return 1;
      case kDtDeviceIdFlashCtrl:
        return 0;
      case kDtDeviceIdRvDm:
        return 0;
      case kDtDeviceIdRvPlic:
        return 0;
      case kDtDeviceIdAes:
        return 0;
      case kDtDeviceIdHmac:
        return 0;
      case kDtDeviceIdKmac:
        return 0;
      case kDtDeviceIdOtbn:
        return 0;
      case kDtDeviceIdKeymgr:
        return 0;
      case kDtDeviceIdCsrng:
        return 0;
      case kDtDeviceIdEntropySrc:
        return 0;
      case kDtDeviceIdEdn0:
        return 0;
      case kDtDeviceIdEdn1:
        return 1;
      case kDtDeviceIdRomCtrl:
        return 0;
      case kDtDeviceIdRvCoreIbex:
        return 0;
      default:
        break;
    }
  }
  return 0;
}

dt_device_type_t dt_device_get_type(dt_device_t dev) {
  return __dt_device_get_type(dev);
}

uintptr_t dt_device_reg_addr(dt_device_t dev, uint32_t reg_block_idx) {
  if (dev < kDtDeviceIdCount) {
    uint32_t dev_idx = __dt_device_get_index(dev);
    dt_device_type_t dev_type = __dt_device_get_type(dev);
    if (dev_type < kDtDeviceTypeCount) {
      switch (dev_type) {
        case kDtDeviceTypeAdcCtrl:
          if (reg_block_idx < kDtAdcCtrlRegBlockCount) {
              return dev_table_adc_ctrl[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeAes:
          if (reg_block_idx < kDtAesRegBlockCount) {
              return dev_table_aes[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeAlertHandler:
          if (reg_block_idx < kDtAlertHandlerRegBlockCount) {
              return dev_table_alert_handler[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeAonTimer:
          if (reg_block_idx < kDtAonTimerRegBlockCount) {
              return dev_table_aon_timer[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeClkmgr:
          if (reg_block_idx < kDtClkmgrRegBlockCount) {
              return dev_table_clkmgr[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeCsrng:
          if (reg_block_idx < kDtCsrngRegBlockCount) {
              return dev_table_csrng[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeEdn:
          if (reg_block_idx < kDtEdnRegBlockCount) {
              return dev_table_edn[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeEntropySrc:
          if (reg_block_idx < kDtEntropySrcRegBlockCount) {
              return dev_table_entropy_src[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeFlashCtrl:
          if (reg_block_idx < kDtFlashCtrlRegBlockCount) {
              return dev_table_flash_ctrl[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeGpio:
          if (reg_block_idx < kDtGpioRegBlockCount) {
              return dev_table_gpio[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeHmac:
          if (reg_block_idx < kDtHmacRegBlockCount) {
              return dev_table_hmac[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeI2c:
          if (reg_block_idx < kDtI2cRegBlockCount) {
              return dev_table_i2c[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeKeymgr:
          if (reg_block_idx < kDtKeymgrRegBlockCount) {
              return dev_table_keymgr[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeKmac:
          if (reg_block_idx < kDtKmacRegBlockCount) {
              return dev_table_kmac[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeLcCtrl:
          if (reg_block_idx < kDtLcCtrlRegBlockCount) {
              return dev_table_lc_ctrl[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeOtbn:
          if (reg_block_idx < kDtOtbnRegBlockCount) {
              return dev_table_otbn[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeOtpCtrl:
          if (reg_block_idx < kDtOtpCtrlRegBlockCount) {
              return dev_table_otp_ctrl[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypePattgen:
          if (reg_block_idx < kDtPattgenRegBlockCount) {
              return dev_table_pattgen[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypePinmux:
          if (reg_block_idx < kDtPinmuxRegBlockCount) {
              return dev_table_pinmux[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypePwm:
          if (reg_block_idx < kDtPwmRegBlockCount) {
              return dev_table_pwm[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypePwrmgr:
          if (reg_block_idx < kDtPwrmgrRegBlockCount) {
              return dev_table_pwrmgr[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeRomCtrl:
          if (reg_block_idx < kDtRomCtrlRegBlockCount) {
              return dev_table_rom_ctrl[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeRstmgr:
          if (reg_block_idx < kDtRstmgrRegBlockCount) {
              return dev_table_rstmgr[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeRvCoreIbex:
          if (reg_block_idx < kDtRvCoreIbexRegBlockCount) {
              return dev_table_rv_core_ibex[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeRvDm:
          if (reg_block_idx < kDtRvDmRegBlockCount) {
              return dev_table_rv_dm[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeRvPlic:
          if (reg_block_idx < kDtRvPlicRegBlockCount) {
              return dev_table_rv_plic[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeRvTimer:
          if (reg_block_idx < kDtRvTimerRegBlockCount) {
              return dev_table_rv_timer[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeSpiDevice:
          if (reg_block_idx < kDtSpiDeviceRegBlockCount) {
              return dev_table_spi_device[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeSpiHost:
          if (reg_block_idx < kDtSpiHostRegBlockCount) {
              return dev_table_spi_host[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeSramCtrl:
          if (reg_block_idx < kDtSramCtrlRegBlockCount) {
              return dev_table_sram_ctrl[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeSysrstCtrl:
          if (reg_block_idx < kDtSysrstCtrlRegBlockCount) {
              return dev_table_sysrst_ctrl[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeUart:
          if (reg_block_idx < kDtUartRegBlockCount) {
              return dev_table_uart[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        case kDtDeviceTypeUsbdev:
          if (reg_block_idx < kDtUsbdevRegBlockCount) {
              return dev_table_usbdev[dev_idx].base_addrs[reg_block_idx];
          }
          break;
        default:
          break;
      }
    }
  }
  return 0;
}

uint32_t dt_device_irq_id(dt_device_t dev, uint32_t irq_type) {
  if (dev < kDtDeviceIdCount) {
    uint32_t dev_idx = __dt_device_get_index(dev);
    dt_device_type_t dev_type = __dt_device_get_type(dev);
    if (dev_type < kDtDeviceTypeCount) {
      switch (dev_type) {
        case kDtDeviceTypeAdcCtrl:
          if (irq_type < kDtAdcCtrlIrqTypeCount) {
              return dev_table_adc_ctrl[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeAlertHandler:
          if (irq_type < kDtAlertHandlerIrqTypeCount) {
              return dev_table_alert_handler[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeAonTimer:
          if (irq_type < kDtAonTimerIrqTypeCount) {
              return dev_table_aon_timer[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeCsrng:
          if (irq_type < kDtCsrngIrqTypeCount) {
              return dev_table_csrng[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeEdn:
          if (irq_type < kDtEdnIrqTypeCount) {
              return dev_table_edn[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeEntropySrc:
          if (irq_type < kDtEntropySrcIrqTypeCount) {
              return dev_table_entropy_src[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeFlashCtrl:
          if (irq_type < kDtFlashCtrlIrqTypeCount) {
              return dev_table_flash_ctrl[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeGpio:
          if (irq_type < kDtGpioIrqTypeCount) {
              return dev_table_gpio[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeHmac:
          if (irq_type < kDtHmacIrqTypeCount) {
              return dev_table_hmac[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeI2c:
          if (irq_type < kDtI2cIrqTypeCount) {
              return dev_table_i2c[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeKeymgr:
          if (irq_type < kDtKeymgrIrqTypeCount) {
              return dev_table_keymgr[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeKmac:
          if (irq_type < kDtKmacIrqTypeCount) {
              return dev_table_kmac[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeOtbn:
          if (irq_type < kDtOtbnIrqTypeCount) {
              return dev_table_otbn[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeOtpCtrl:
          if (irq_type < kDtOtpCtrlIrqTypeCount) {
              return dev_table_otp_ctrl[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypePattgen:
          if (irq_type < kDtPattgenIrqTypeCount) {
              return dev_table_pattgen[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypePwrmgr:
          if (irq_type < kDtPwrmgrIrqTypeCount) {
              return dev_table_pwrmgr[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeRvTimer:
          if (irq_type < kDtRvTimerIrqTypeCount) {
              return dev_table_rv_timer[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeSpiDevice:
          if (irq_type < kDtSpiDeviceIrqTypeCount) {
              return dev_table_spi_device[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeSpiHost:
          if (irq_type < kDtSpiHostIrqTypeCount) {
              return dev_table_spi_host[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeSysrstCtrl:
          if (irq_type < kDtSysrstCtrlIrqTypeCount) {
              return dev_table_sysrst_ctrl[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeUart:
          if (irq_type < kDtUartIrqTypeCount) {
              return dev_table_uart[dev_idx].irqs[irq_type];
          }
          break;
        case kDtDeviceTypeUsbdev:
          if (irq_type < kDtUsbdevIrqTypeCount) {
              return dev_table_usbdev[dev_idx].irqs[irq_type];
          }
          break;
        default:
          break;
      }
    }
  }
  return kDtIrqUnknown;
}

dt_clock_t dt_device_clock_id(dt_device_t dev, uint32_t clock_port) {
  if (dev < kDtDeviceIdCount) {
    uint32_t dev_idx = __dt_device_get_index(dev);
    dt_device_type_t dev_type = __dt_device_get_type(dev);
    if (dev_type < kDtDeviceTypeCount) {
      switch (dev_type) {
        case kDtDeviceTypeAdcCtrl:
          if (clock_port < kDtAdcCtrlClockCount) {
              return dev_table_adc_ctrl[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeAes:
          if (clock_port < kDtAesClockCount) {
              return dev_table_aes[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeAlertHandler:
          if (clock_port < kDtAlertHandlerClockCount) {
              return dev_table_alert_handler[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeAonTimer:
          if (clock_port < kDtAonTimerClockCount) {
              return dev_table_aon_timer[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeClkmgr:
          if (clock_port < kDtClkmgrClockCount) {
              return dev_table_clkmgr[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeCsrng:
          if (clock_port < kDtCsrngClockCount) {
              return dev_table_csrng[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeEdn:
          if (clock_port < kDtEdnClockCount) {
              return dev_table_edn[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeEntropySrc:
          if (clock_port < kDtEntropySrcClockCount) {
              return dev_table_entropy_src[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeFlashCtrl:
          if (clock_port < kDtFlashCtrlClockCount) {
              return dev_table_flash_ctrl[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeGpio:
          if (clock_port < kDtGpioClockCount) {
              return dev_table_gpio[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeHmac:
          if (clock_port < kDtHmacClockCount) {
              return dev_table_hmac[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeI2c:
          if (clock_port < kDtI2cClockCount) {
              return dev_table_i2c[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeKeymgr:
          if (clock_port < kDtKeymgrClockCount) {
              return dev_table_keymgr[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeKmac:
          if (clock_port < kDtKmacClockCount) {
              return dev_table_kmac[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeLcCtrl:
          if (clock_port < kDtLcCtrlClockCount) {
              return dev_table_lc_ctrl[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeOtbn:
          if (clock_port < kDtOtbnClockCount) {
              return dev_table_otbn[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeOtpCtrl:
          if (clock_port < kDtOtpCtrlClockCount) {
              return dev_table_otp_ctrl[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypePattgen:
          if (clock_port < kDtPattgenClockCount) {
              return dev_table_pattgen[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypePinmux:
          if (clock_port < kDtPinmuxClockCount) {
              return dev_table_pinmux[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypePwm:
          if (clock_port < kDtPwmClockCount) {
              return dev_table_pwm[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypePwrmgr:
          if (clock_port < kDtPwrmgrClockCount) {
              return dev_table_pwrmgr[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeRomCtrl:
          if (clock_port < kDtRomCtrlClockCount) {
              return dev_table_rom_ctrl[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeRstmgr:
          if (clock_port < kDtRstmgrClockCount) {
              return dev_table_rstmgr[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeRvCoreIbex:
          if (clock_port < kDtRvCoreIbexClockCount) {
              return dev_table_rv_core_ibex[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeRvDm:
          if (clock_port < kDtRvDmClockCount) {
              return dev_table_rv_dm[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeRvPlic:
          if (clock_port < kDtRvPlicClockCount) {
              return dev_table_rv_plic[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeRvTimer:
          if (clock_port < kDtRvTimerClockCount) {
              return dev_table_rv_timer[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeSpiDevice:
          if (clock_port < kDtSpiDeviceClockCount) {
              return dev_table_spi_device[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeSpiHost:
          if (clock_port < kDtSpiHostClockCount) {
              return dev_table_spi_host[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeSramCtrl:
          if (clock_port < kDtSramCtrlClockCount) {
              return dev_table_sram_ctrl[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeSysrstCtrl:
          if (clock_port < kDtSysrstCtrlClockCount) {
              return dev_table_sysrst_ctrl[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeUart:
          if (clock_port < kDtUartClockCount) {
              return dev_table_uart[dev_idx].clocks[clock_port];
          }
          break;
        case kDtDeviceTypeUsbdev:
          if (clock_port < kDtUsbdevClockCount) {
              return dev_table_usbdev[dev_idx].clocks[clock_port];
          }
          break;
        default:
          break;
      }
    }
  }
  return kDtClockUnknown;
}

enum {
  kDtIrqIdCount = 182,
};

static const dt_device_t device_from_irq[kDtIrqIdCount] = {
    [kTopEarlgreyPlicIrqIdNone] = kDtDeviceIdUnknown,
    [kTopEarlgreyPlicIrqIdUart0TxWatermark] = kDtDeviceIdUart0,
    [kTopEarlgreyPlicIrqIdUart0RxWatermark] = kDtDeviceIdUart0,
    [kTopEarlgreyPlicIrqIdUart0TxEmpty] = kDtDeviceIdUart0,
    [kTopEarlgreyPlicIrqIdUart0RxOverflow] = kDtDeviceIdUart0,
    [kTopEarlgreyPlicIrqIdUart0RxFrameErr] = kDtDeviceIdUart0,
    [kTopEarlgreyPlicIrqIdUart0RxBreakErr] = kDtDeviceIdUart0,
    [kTopEarlgreyPlicIrqIdUart0RxTimeout] = kDtDeviceIdUart0,
    [kTopEarlgreyPlicIrqIdUart0RxParityErr] = kDtDeviceIdUart0,
    [kTopEarlgreyPlicIrqIdUart1TxWatermark] = kDtDeviceIdUart1,
    [kTopEarlgreyPlicIrqIdUart1RxWatermark] = kDtDeviceIdUart1,
    [kTopEarlgreyPlicIrqIdUart1TxEmpty] = kDtDeviceIdUart1,
    [kTopEarlgreyPlicIrqIdUart1RxOverflow] = kDtDeviceIdUart1,
    [kTopEarlgreyPlicIrqIdUart1RxFrameErr] = kDtDeviceIdUart1,
    [kTopEarlgreyPlicIrqIdUart1RxBreakErr] = kDtDeviceIdUart1,
    [kTopEarlgreyPlicIrqIdUart1RxTimeout] = kDtDeviceIdUart1,
    [kTopEarlgreyPlicIrqIdUart1RxParityErr] = kDtDeviceIdUart1,
    [kTopEarlgreyPlicIrqIdUart2TxWatermark] = kDtDeviceIdUart2,
    [kTopEarlgreyPlicIrqIdUart2RxWatermark] = kDtDeviceIdUart2,
    [kTopEarlgreyPlicIrqIdUart2TxEmpty] = kDtDeviceIdUart2,
    [kTopEarlgreyPlicIrqIdUart2RxOverflow] = kDtDeviceIdUart2,
    [kTopEarlgreyPlicIrqIdUart2RxFrameErr] = kDtDeviceIdUart2,
    [kTopEarlgreyPlicIrqIdUart2RxBreakErr] = kDtDeviceIdUart2,
    [kTopEarlgreyPlicIrqIdUart2RxTimeout] = kDtDeviceIdUart2,
    [kTopEarlgreyPlicIrqIdUart2RxParityErr] = kDtDeviceIdUart2,
    [kTopEarlgreyPlicIrqIdUart3TxWatermark] = kDtDeviceIdUart3,
    [kTopEarlgreyPlicIrqIdUart3RxWatermark] = kDtDeviceIdUart3,
    [kTopEarlgreyPlicIrqIdUart3TxEmpty] = kDtDeviceIdUart3,
    [kTopEarlgreyPlicIrqIdUart3RxOverflow] = kDtDeviceIdUart3,
    [kTopEarlgreyPlicIrqIdUart3RxFrameErr] = kDtDeviceIdUart3,
    [kTopEarlgreyPlicIrqIdUart3RxBreakErr] = kDtDeviceIdUart3,
    [kTopEarlgreyPlicIrqIdUart3RxTimeout] = kDtDeviceIdUart3,
    [kTopEarlgreyPlicIrqIdUart3RxParityErr] = kDtDeviceIdUart3,
    [kTopEarlgreyPlicIrqIdGpioGpio0] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio1] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio2] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio3] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio4] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio5] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio6] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio7] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio8] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio9] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio10] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio11] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio12] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio13] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio14] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio15] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio16] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio17] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio18] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio19] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio20] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio21] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio22] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio23] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio24] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio25] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio26] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio27] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio28] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio29] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio30] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdGpioGpio31] = kDtDeviceIdGpio,
    [kTopEarlgreyPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty] = kDtDeviceIdSpiDevice,
    [kTopEarlgreyPlicIrqIdSpiDeviceUploadPayloadNotEmpty] = kDtDeviceIdSpiDevice,
    [kTopEarlgreyPlicIrqIdSpiDeviceUploadPayloadOverflow] = kDtDeviceIdSpiDevice,
    [kTopEarlgreyPlicIrqIdSpiDeviceReadbufWatermark] = kDtDeviceIdSpiDevice,
    [kTopEarlgreyPlicIrqIdSpiDeviceReadbufFlip] = kDtDeviceIdSpiDevice,
    [kTopEarlgreyPlicIrqIdSpiDeviceTpmHeaderNotEmpty] = kDtDeviceIdSpiDevice,
    [kTopEarlgreyPlicIrqIdSpiDeviceTpmRdfifoCmdEnd] = kDtDeviceIdSpiDevice,
    [kTopEarlgreyPlicIrqIdSpiDeviceTpmRdfifoDrop] = kDtDeviceIdSpiDevice,
    [kTopEarlgreyPlicIrqIdI2c0FmtThreshold] = kDtDeviceIdI2c0,
    [kTopEarlgreyPlicIrqIdI2c0RxThreshold] = kDtDeviceIdI2c0,
    [kTopEarlgreyPlicIrqIdI2c0AcqThreshold] = kDtDeviceIdI2c0,
    [kTopEarlgreyPlicIrqIdI2c0RxOverflow] = kDtDeviceIdI2c0,
    [kTopEarlgreyPlicIrqIdI2c0Nak] = kDtDeviceIdI2c0,
    [kTopEarlgreyPlicIrqIdI2c0SclInterference] = kDtDeviceIdI2c0,
    [kTopEarlgreyPlicIrqIdI2c0SdaInterference] = kDtDeviceIdI2c0,
    [kTopEarlgreyPlicIrqIdI2c0StretchTimeout] = kDtDeviceIdI2c0,
    [kTopEarlgreyPlicIrqIdI2c0SdaUnstable] = kDtDeviceIdI2c0,
    [kTopEarlgreyPlicIrqIdI2c0CmdComplete] = kDtDeviceIdI2c0,
    [kTopEarlgreyPlicIrqIdI2c0TxStretch] = kDtDeviceIdI2c0,
    [kTopEarlgreyPlicIrqIdI2c0TxThreshold] = kDtDeviceIdI2c0,
    [kTopEarlgreyPlicIrqIdI2c0AcqFull] = kDtDeviceIdI2c0,
    [kTopEarlgreyPlicIrqIdI2c0UnexpStop] = kDtDeviceIdI2c0,
    [kTopEarlgreyPlicIrqIdI2c0HostTimeout] = kDtDeviceIdI2c0,
    [kTopEarlgreyPlicIrqIdI2c1FmtThreshold] = kDtDeviceIdI2c1,
    [kTopEarlgreyPlicIrqIdI2c1RxThreshold] = kDtDeviceIdI2c1,
    [kTopEarlgreyPlicIrqIdI2c1AcqThreshold] = kDtDeviceIdI2c1,
    [kTopEarlgreyPlicIrqIdI2c1RxOverflow] = kDtDeviceIdI2c1,
    [kTopEarlgreyPlicIrqIdI2c1Nak] = kDtDeviceIdI2c1,
    [kTopEarlgreyPlicIrqIdI2c1SclInterference] = kDtDeviceIdI2c1,
    [kTopEarlgreyPlicIrqIdI2c1SdaInterference] = kDtDeviceIdI2c1,
    [kTopEarlgreyPlicIrqIdI2c1StretchTimeout] = kDtDeviceIdI2c1,
    [kTopEarlgreyPlicIrqIdI2c1SdaUnstable] = kDtDeviceIdI2c1,
    [kTopEarlgreyPlicIrqIdI2c1CmdComplete] = kDtDeviceIdI2c1,
    [kTopEarlgreyPlicIrqIdI2c1TxStretch] = kDtDeviceIdI2c1,
    [kTopEarlgreyPlicIrqIdI2c1TxThreshold] = kDtDeviceIdI2c1,
    [kTopEarlgreyPlicIrqIdI2c1AcqFull] = kDtDeviceIdI2c1,
    [kTopEarlgreyPlicIrqIdI2c1UnexpStop] = kDtDeviceIdI2c1,
    [kTopEarlgreyPlicIrqIdI2c1HostTimeout] = kDtDeviceIdI2c1,
    [kTopEarlgreyPlicIrqIdI2c2FmtThreshold] = kDtDeviceIdI2c2,
    [kTopEarlgreyPlicIrqIdI2c2RxThreshold] = kDtDeviceIdI2c2,
    [kTopEarlgreyPlicIrqIdI2c2AcqThreshold] = kDtDeviceIdI2c2,
    [kTopEarlgreyPlicIrqIdI2c2RxOverflow] = kDtDeviceIdI2c2,
    [kTopEarlgreyPlicIrqIdI2c2Nak] = kDtDeviceIdI2c2,
    [kTopEarlgreyPlicIrqIdI2c2SclInterference] = kDtDeviceIdI2c2,
    [kTopEarlgreyPlicIrqIdI2c2SdaInterference] = kDtDeviceIdI2c2,
    [kTopEarlgreyPlicIrqIdI2c2StretchTimeout] = kDtDeviceIdI2c2,
    [kTopEarlgreyPlicIrqIdI2c2SdaUnstable] = kDtDeviceIdI2c2,
    [kTopEarlgreyPlicIrqIdI2c2CmdComplete] = kDtDeviceIdI2c2,
    [kTopEarlgreyPlicIrqIdI2c2TxStretch] = kDtDeviceIdI2c2,
    [kTopEarlgreyPlicIrqIdI2c2TxThreshold] = kDtDeviceIdI2c2,
    [kTopEarlgreyPlicIrqIdI2c2AcqFull] = kDtDeviceIdI2c2,
    [kTopEarlgreyPlicIrqIdI2c2UnexpStop] = kDtDeviceIdI2c2,
    [kTopEarlgreyPlicIrqIdI2c2HostTimeout] = kDtDeviceIdI2c2,
    [kTopEarlgreyPlicIrqIdPattgenDoneCh0] = kDtDeviceIdPattgen,
    [kTopEarlgreyPlicIrqIdPattgenDoneCh1] = kDtDeviceIdPattgen,
    [kTopEarlgreyPlicIrqIdRvTimerTimerExpiredHart0Timer0] = kDtDeviceIdRvTimer,
    [kTopEarlgreyPlicIrqIdOtpCtrlOtpOperationDone] = kDtDeviceIdOtpCtrl,
    [kTopEarlgreyPlicIrqIdOtpCtrlOtpError] = kDtDeviceIdOtpCtrl,
    [kTopEarlgreyPlicIrqIdAlertHandlerClassa] = kDtDeviceIdAlertHandler,
    [kTopEarlgreyPlicIrqIdAlertHandlerClassb] = kDtDeviceIdAlertHandler,
    [kTopEarlgreyPlicIrqIdAlertHandlerClassc] = kDtDeviceIdAlertHandler,
    [kTopEarlgreyPlicIrqIdAlertHandlerClassd] = kDtDeviceIdAlertHandler,
    [kTopEarlgreyPlicIrqIdSpiHost0Error] = kDtDeviceIdSpiHost0,
    [kTopEarlgreyPlicIrqIdSpiHost0SpiEvent] = kDtDeviceIdSpiHost0,
    [kTopEarlgreyPlicIrqIdSpiHost1Error] = kDtDeviceIdSpiHost1,
    [kTopEarlgreyPlicIrqIdSpiHost1SpiEvent] = kDtDeviceIdSpiHost1,
    [kTopEarlgreyPlicIrqIdUsbdevPktReceived] = kDtDeviceIdUsbdev,
    [kTopEarlgreyPlicIrqIdUsbdevPktSent] = kDtDeviceIdUsbdev,
    [kTopEarlgreyPlicIrqIdUsbdevDisconnected] = kDtDeviceIdUsbdev,
    [kTopEarlgreyPlicIrqIdUsbdevHostLost] = kDtDeviceIdUsbdev,
    [kTopEarlgreyPlicIrqIdUsbdevLinkReset] = kDtDeviceIdUsbdev,
    [kTopEarlgreyPlicIrqIdUsbdevLinkSuspend] = kDtDeviceIdUsbdev,
    [kTopEarlgreyPlicIrqIdUsbdevLinkResume] = kDtDeviceIdUsbdev,
    [kTopEarlgreyPlicIrqIdUsbdevAvOutEmpty] = kDtDeviceIdUsbdev,
    [kTopEarlgreyPlicIrqIdUsbdevRxFull] = kDtDeviceIdUsbdev,
    [kTopEarlgreyPlicIrqIdUsbdevAvOverflow] = kDtDeviceIdUsbdev,
    [kTopEarlgreyPlicIrqIdUsbdevLinkInErr] = kDtDeviceIdUsbdev,
    [kTopEarlgreyPlicIrqIdUsbdevRxCrcErr] = kDtDeviceIdUsbdev,
    [kTopEarlgreyPlicIrqIdUsbdevRxPidErr] = kDtDeviceIdUsbdev,
    [kTopEarlgreyPlicIrqIdUsbdevRxBitstuffErr] = kDtDeviceIdUsbdev,
    [kTopEarlgreyPlicIrqIdUsbdevFrame] = kDtDeviceIdUsbdev,
    [kTopEarlgreyPlicIrqIdUsbdevPowered] = kDtDeviceIdUsbdev,
    [kTopEarlgreyPlicIrqIdUsbdevLinkOutErr] = kDtDeviceIdUsbdev,
    [kTopEarlgreyPlicIrqIdUsbdevAvSetupEmpty] = kDtDeviceIdUsbdev,
    [kTopEarlgreyPlicIrqIdPwrmgrAonWakeup] = kDtDeviceIdPwrmgrAon,
    [kTopEarlgreyPlicIrqIdSysrstCtrlAonEventDetected] = kDtDeviceIdSysrstCtrlAon,
    [kTopEarlgreyPlicIrqIdAdcCtrlAonMatchDone] = kDtDeviceIdAdcCtrlAon,
    [kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired] = kDtDeviceIdAonTimerAon,
    [kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark] = kDtDeviceIdAonTimerAon,
    [kTopEarlgreyPlicIrqIdSensorCtrlAonIoStatusChange] = kDtDeviceIdSensorCtrlAon,
    [kTopEarlgreyPlicIrqIdSensorCtrlAonInitStatusChange] = kDtDeviceIdSensorCtrlAon,
    [kTopEarlgreyPlicIrqIdFlashCtrlProgEmpty] = kDtDeviceIdFlashCtrl,
    [kTopEarlgreyPlicIrqIdFlashCtrlProgLvl] = kDtDeviceIdFlashCtrl,
    [kTopEarlgreyPlicIrqIdFlashCtrlRdFull] = kDtDeviceIdFlashCtrl,
    [kTopEarlgreyPlicIrqIdFlashCtrlRdLvl] = kDtDeviceIdFlashCtrl,
    [kTopEarlgreyPlicIrqIdFlashCtrlOpDone] = kDtDeviceIdFlashCtrl,
    [kTopEarlgreyPlicIrqIdFlashCtrlCorrErr] = kDtDeviceIdFlashCtrl,
    [kTopEarlgreyPlicIrqIdHmacHmacDone] = kDtDeviceIdHmac,
    [kTopEarlgreyPlicIrqIdHmacFifoEmpty] = kDtDeviceIdHmac,
    [kTopEarlgreyPlicIrqIdHmacHmacErr] = kDtDeviceIdHmac,
    [kTopEarlgreyPlicIrqIdKmacKmacDone] = kDtDeviceIdKmac,
    [kTopEarlgreyPlicIrqIdKmacFifoEmpty] = kDtDeviceIdKmac,
    [kTopEarlgreyPlicIrqIdKmacKmacErr] = kDtDeviceIdKmac,
    [kTopEarlgreyPlicIrqIdOtbnDone] = kDtDeviceIdOtbn,
    [kTopEarlgreyPlicIrqIdKeymgrOpDone] = kDtDeviceIdKeymgr,
    [kTopEarlgreyPlicIrqIdCsrngCsCmdReqDone] = kDtDeviceIdCsrng,
    [kTopEarlgreyPlicIrqIdCsrngCsEntropyReq] = kDtDeviceIdCsrng,
    [kTopEarlgreyPlicIrqIdCsrngCsHwInstExc] = kDtDeviceIdCsrng,
    [kTopEarlgreyPlicIrqIdCsrngCsFatalErr] = kDtDeviceIdCsrng,
    [kTopEarlgreyPlicIrqIdEntropySrcEsEntropyValid] = kDtDeviceIdEntropySrc,
    [kTopEarlgreyPlicIrqIdEntropySrcEsHealthTestFailed] = kDtDeviceIdEntropySrc,
    [kTopEarlgreyPlicIrqIdEntropySrcEsObserveFifoReady] = kDtDeviceIdEntropySrc,
    [kTopEarlgreyPlicIrqIdEntropySrcEsFatalErr] = kDtDeviceIdEntropySrc,
    [kTopEarlgreyPlicIrqIdEdn0EdnCmdReqDone] = kDtDeviceIdEdn0,
    [kTopEarlgreyPlicIrqIdEdn0EdnFatalErr] = kDtDeviceIdEdn0,
    [kTopEarlgreyPlicIrqIdEdn1EdnCmdReqDone] = kDtDeviceIdEdn1,
    [kTopEarlgreyPlicIrqIdEdn1EdnFatalErr] = kDtDeviceIdEdn1,
};

/**
 * Return device ID for a given peripheral
 */
dt_device_t dt_irq_to_device(uint32_t irq) {
  if (irq < kDtIrqIdCount) {
    return device_from_irq[irq];
  }
  return kDtDeviceUnknown;
}
