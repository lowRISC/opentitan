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
 *
 * Internal functions used by libmpsse.
 *
 * Craig Heffner
 * 27 December 2011
 */
#include <stdlib.h>
#include <string.h>

#include "support.h"

/* Write data to the FTDI chip */
int raw_write(struct mpsse_context* mpsse, uint8_t* buf, int size) {
   int retval = MPSSE_FAIL;

   if (mpsse->mode) {
     if (ftdi_write_data(&mpsse->ftdi, buf, size) == size) {
       retval = MPSSE_OK;
     }
   }

   return retval;
 }

 /* Read data from the FTDI chip */
 int raw_read(struct mpsse_context* mpsse, uint8_t* buf, int size) {
   int n = 0, r = 0;

   if (mpsse->mode) {
     while (n < size) {
       r = ftdi_read_data(&mpsse->ftdi, buf, size);
       if (r < 0)
         break;
       n += r;
     }

     if (mpsse->flush_after_read) {
       /*
        * Make sure the buffers are cleared after a read or subsequent reads may
        *fail.
        *
        * Is this needed anymore? It slows down repetitive read operations by
        *~8%.
        */
       ftdi_usb_purge_rx_buffer(&mpsse->ftdi);
     }
   }

   return n;
 }

 /* Sets the read and write timeout periods for bulk usb data transfers. */
 void set_timeouts(struct mpsse_context* mpsse, int timeout) {
   if (mpsse->mode) {
     mpsse->ftdi.usb_read_timeout = timeout;
     mpsse->ftdi.usb_write_timeout = timeout;
   }

   return;
 }

 /* Convert a frequency to a clock divisor */
 uint16_t freq2div(uint32_t system_clock, uint32_t freq) {
   return (((system_clock / freq) / 2) - 1);
 }

 /* Convert a clock divisor to a frequency */
 uint32_t div2freq(uint32_t system_clock, uint16_t div) {
   return (system_clock / ((1 + div) * 2));
 }

 /* Builds a buffer of commands + data blocks */
 uint8_t* build_block_buffer(struct mpsse_context* mpsse,
                             uint8_t cmd,
                             const uint8_t* data,
                             int size,
                             int* buf_size) {
   uint8_t* buf = NULL;
   int i = 0, j = 0, k = 0, dsize = 0, num_blocks = 0, total_size = 0,
       xfer_size = 0;
   uint16_t rsize = 0;

   *buf_size = 0;

   /* Data block size is 1 in I2C, or when in bitmode */
   if (mpsse->mode == I2C || (cmd & MPSSE_BITMODE)) {
     xfer_size = 1;
   } else {
     xfer_size = mpsse->xsize;
   }

   num_blocks = (size / xfer_size);
   if (size % xfer_size) {
     num_blocks++;
   }

   /* The total size of the data will be the data size + the write command */
   total_size = size + (CMD_SIZE * num_blocks);

   /* In I2C we have to add 3 additional commands per data block */
   if (mpsse->mode == I2C) {
     total_size += (CMD_SIZE * 3 * num_blocks);
   }

   buf = malloc(total_size);
   if (buf) {
     memset(buf, 0, total_size);

     for (j = 0; j < num_blocks; j++) {
       dsize = size - k;
       if (dsize > xfer_size) {
         dsize = xfer_size;
       }

       /* The reported size of this block is block size - 1 */
       rsize = dsize - 1;

       /* For I2C we need to ensure that the clock pin is set low prior to
        * clocking out data */
       if (mpsse->mode == I2C) {
         buf[i++] = SET_BITS_LOW;
         buf[i++] = mpsse->pstart & ~SK;

         /* On receive, we need to ensure that the data out line is set as an
          * input to avoid contention on the bus */
         if (cmd == mpsse->rx) {
           buf[i++] = mpsse->tris & ~DO;
         } else {
           buf[i++] = mpsse->tris;
         }
       }

       /* Copy in the command for this block */
       buf[i++] = cmd;
       buf[i++] = (rsize & 0xFF);
       if (!(cmd & MPSSE_BITMODE)) {
         buf[i++] = ((rsize >> 8) & 0xFF);
       }

       /* On a write, copy the data to transmit after the command */
       if (cmd == mpsse->tx || cmd == mpsse->txrx) {
         memcpy(buf + i, data + k, dsize);

         /* i == offset into buf */
         i += dsize;
         /* k == offset into data */
         k += dsize;
       }

       /* In I2C mode we need to clock one ACK bit after each byte */
       if (mpsse->mode == I2C) {
         /* If we are receiving data, then we need to clock out an ACK for each
          * byte */
         if (cmd == mpsse->rx) {
           buf[i++] = SET_BITS_LOW;
           buf[i++] = mpsse->pstart & ~SK;
           buf[i++] = mpsse->tris;

           buf[i++] = mpsse->tx | MPSSE_BITMODE;
           buf[i++] = 0;
           buf[i++] = mpsse->tack;
         }
         /* If we are sending data, then we need to clock in an ACK for each
          * byte
            */
         else if (cmd == mpsse->tx) {
           /* Need to make data out an input to avoid contention on the bus when
            * the slave sends an ACK */
           buf[i++] = SET_BITS_LOW;
           buf[i++] = mpsse->pstart & ~SK;
           buf[i++] = mpsse->tris & ~DO;

           buf[i++] = mpsse->rx | MPSSE_BITMODE;
           buf[i++] = 0;
           buf[i++] = SEND_IMMEDIATE;
         }
       }
     }

     *buf_size = i;
   }

   return buf;
 }

 /* Set the low bit pins high/low */
 int set_bits_low(struct mpsse_context* mpsse, int port) {
   char buf[CMD_SIZE] = {0};

   buf[0] = SET_BITS_LOW;
   buf[1] = port;
   buf[2] = mpsse->tris;

   return raw_write(mpsse, (uint8_t*)&buf, sizeof(buf));
 }

 /* Set the high bit pins high/low */
 int set_bits_high(struct mpsse_context* mpsse, int port) {
   char buf[CMD_SIZE] = {0};

   buf[0] = SET_BITS_HIGH;
   buf[1] = port;
   buf[2] = mpsse->trish;

   return raw_write(mpsse, (uint8_t*)&buf, sizeof(buf));
 }

 /* Set the GPIO pins high/low */
 int gpio_write(struct mpsse_context* mpsse, int pin, int direction) {
   int retval = MPSSE_FAIL;

   if (mpsse->mode == BITBANG) {
     if (direction == HIGH) {
       mpsse->bitbang |= (1 << pin);
     } else {
       mpsse->bitbang &= ~(1 << pin);
     }

     if (set_bits_high(mpsse, mpsse->bitbang) == MPSSE_OK) {
       retval = raw_write(mpsse, (uint8_t*)&mpsse->bitbang, 1);
     }
   } else {
     /* The first four pins can't be changed unless we are in a stopped status
      */
     if (pin < NUM_GPIOL_PINS && mpsse->status == STOPPED) {
       /* Convert pin number (0-3) to the corresponding pin bit */
       pin = (GPIO0 << pin);

       if (direction == HIGH) {
         mpsse->pstart |= pin;
         mpsse->pidle |= pin;
         mpsse->pstop |= pin;
       } else {
         mpsse->pstart &= ~pin;
         mpsse->pidle &= ~pin;
         mpsse->pstop &= ~pin;
       }

       retval = set_bits_low(mpsse, mpsse->pstop);
     } else if (pin >= NUM_GPIOL_PINS && pin < NUM_GPIO_PINS) {
       /* Convert pin number (4 - 11) to the corresponding pin bit */
       pin -= NUM_GPIOL_PINS;

       if (direction == HIGH) {
         mpsse->gpioh |= (1 << pin);
       } else {
         mpsse->gpioh &= ~(1 << pin);
       }

       retval = set_bits_high(mpsse, mpsse->gpioh);
     }
   }

   return retval;
 }

 /* Checks if a given MPSSE context is valid. */
 int is_valid_context(struct mpsse_context* mpsse) {
   return mpsse != NULL;
 }
