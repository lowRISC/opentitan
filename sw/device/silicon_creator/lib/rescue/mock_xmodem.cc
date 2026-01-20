// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/rescue/mock_xmodem.h"

namespace rom_test {
extern "C" {

void xmodem_recv_start(void *iohandle) {
  MockXmodem::Instance().RecvStart(iohandle);
}

void xmodem_ack(void *iohandle, bool ack) {
  MockXmodem::Instance().Ack(iohandle, ack);
}

void xmodem_cancel(void *iohandle) { MockXmodem::Instance().Cancel(iohandle); }

rom_error_t xmodem_recv_frame(void *iohandle, uint32_t frame, uint8_t *data,
                              size_t len_available, size_t *rxlen,
                              uint8_t *unknown_rx) {
  return MockXmodem::Instance().RecvFrame(iohandle, frame, data, len_available,
                                          rxlen, unknown_rx);
}

rom_error_t xmodem_send(void *iohandle, const void *data, size_t len) {
  return MockXmodem::Instance().Send(iohandle, data, len);
}

}  // extern "C"
}  // namespace rom_test
