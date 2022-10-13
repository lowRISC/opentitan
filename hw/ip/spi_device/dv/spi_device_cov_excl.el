// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

CHECKSUM: "3457538146 2016807823"

ANNOTATION: "[UNSUPPORTED] Mbyte feature isn't supported"
MODULE: spi_passthrough
Fsm st "2016807823"
Transition StMByte->StHighZ "6->4"
Fsm st "2016807823"
Transition StAddress->StMByte "5->6"
CHECKSUM: "869811325 1167994761"
MODULE: spi_readcmd
Fsm main_st "1167994761"
State MainMByte "2"
