// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// Num of valid host source id bits, the upper bits should be tied to zero
parameter int Valid_host_id_lsb  = 2;

// List of Xbar device memory map
tl_device_t xbar_devices[$] = '{'{"TlSram", 'h1000_0000, 'h1000_ffff},
                                '{"TlUart", 'h4000_0000, 'h4000_ffff},
                                '{"TlGpio", 'h4001_0000, 'h4001_ffff}};

// List of Xbar hosts
tl_host_t xbar_hosts[$] = '{'{"TlCoreI", 0, '{"TlSram"}},
                            '{"TlCoreD", 1, '{"TlSram", "TlUart", "TlGpio"}},
                            '{"TlDebugSba", 2, '{"TlSram"}}};
