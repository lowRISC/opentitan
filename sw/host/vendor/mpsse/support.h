/*
** Copyright (C) 2015 The Android Open Source Project
**
** Licensed under the Apache License, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
**      http://www.apache.org/licenses/LICENSE-2.0
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
**/
/*
 * This file was copied from https://github.com/devttys0/libmpsse.git (sha1
 * f1a6744b), and modified to suite the Chromium OS project.
 */

#ifndef TRUNKS_FTDI_SUPPORT_H_
#define TRUNKS_FTDI_SUPPORT_H_

#include <stddef.h>

#include "mpsse.h"

int raw_write(struct mpsse_context* mpsse, uint8_t* buf, int size);
int raw_read(struct mpsse_context* mpsse, uint8_t* buf, int size);
void set_timeouts(struct mpsse_context* mpsse, int timeout);
uint16_t freq2div(uint32_t system_clock, uint32_t freq);
uint32_t div2freq(uint32_t system_clock, uint16_t div);
uint8_t* build_block_buffer(struct mpsse_context* mpsse,
                            uint8_t cmd,
                            const uint8_t* data,
                            int size,
                            int* buf_size);
int set_bits_high(struct mpsse_context* mpsse, int port);
int set_bits_low(struct mpsse_context* mpsse, int port);
int gpio_write(struct mpsse_context* mpsse, int pin, int direction);
int is_valid_context(struct mpsse_context* mpsse);

#endif /*  TRUNKS_FTDI_SUPPORT_H_ */
