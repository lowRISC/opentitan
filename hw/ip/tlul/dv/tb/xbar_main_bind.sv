// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this file should be auto-generated when TB automation is done
module xbar_main_bind;

  `BIND_ASSERT_TL_HOST(corei)
  `BIND_ASSERT_TL_HOST(cored)
  `BIND_ASSERT_TL_HOST(dm_sba)
  `BIND_ASSERT_TL_DEVICE(rom)
  `BIND_ASSERT_TL_DEVICE(debug_mem)
  `BIND_ASSERT_TL_DEVICE(ram_main)
  `BIND_ASSERT_TL_DEVICE(eflash)
  `BIND_ASSERT_TL_DEVICE(uart)
  `BIND_ASSERT_TL_DEVICE(gpio)
  `BIND_ASSERT_TL_DEVICE(spi_device)
  `BIND_ASSERT_TL_DEVICE(flash_ctrl)
  `BIND_ASSERT_TL_DEVICE(rv_timer)
  `BIND_ASSERT_TL_DEVICE(aes)
  `BIND_ASSERT_TL_DEVICE(hmac)
  `BIND_ASSERT_TL_DEVICE(rv_plic)
  `BIND_ASSERT_TL_DEVICE(pinmux)

endmodule
