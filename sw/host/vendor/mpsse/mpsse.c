/*
 *Copyright (C) 2015 The Android Open Source Project
 *
 *Licensed under the Apache License, Version 2.0 (the "License");
 *you may not use this file except in compliance with the License.
 *You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 *Unless required by applicable law or agreed to in writing, software
 *distributed under the License is distributed on an "AS IS" BASIS,
 *WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *See the License for the specific language governing permissions and
 *limitations under the License.
 *
 * This file was copied from https://github.com/devttys0/libmpsse.git (sha1
 * f1a6744b), and modified to suite the Chromium OS project.
 *
 * Main libmpsse source file.
 *
 * Craig Heffner
 * 27 December 2011
 */

#define _XOPEN_SOURCE 500
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>

#include "support.h"

/* List of known FT2232-based devices */
struct vid_pid supported_devices[] = {
    {0x0403, 0x6010, "FT2232 Future Technology Devices International, Ltd"},
    {0x0403, 0x6011, "FT4232 Future Technology Devices International, Ltd"},
    {0x0403, 0x6014, "FT232H Future Technology Devices International, Ltd"},

    /* These devices are based on FT2232 chips, but have not been tested. */
    {0x0403, 0x8878, "Bus Blaster v2 (channel A)"},
    {0x0403, 0x8879, "Bus Blaster v2 (channel B)"},
    {0x0403, 0xBDC8, "Turtelizer JTAG/RS232 Adapter A"},
    {0x0403, 0xCFF8, "Amontec JTAGkey"},
    {0x0403, 0x8A98, "TIAO Multi Protocol Adapter"},
    {0x15BA, 0x0003, "Olimex Ltd. OpenOCD JTAG"},
    {0x15BA, 0x0004, "Olimex Ltd. OpenOCD JTAG TINY"},

    {0, 0, NULL}};

/*
 * Opens and initializes the first FTDI device found.
 *
 * @mode      - Mode to open the device in. One of enum modes.
 * @freq      - Clock frequency to use for the specified mode.
 * @endianess - Specifies how data is clocked in/out (MSB, LSB).
 *
 * Returns a pointer to an MPSSE context structure if succeeded, NULL otherwise.
 */
struct mpsse_context* MPSSE(enum modes mode, int freq, int endianess) {
  int i = 0;
  struct mpsse_context* mpsse = NULL;

  for (i = 0; supported_devices[i].vid != 0; i++) {
    mpsse = Open(supported_devices[i].vid, supported_devices[i].pid, mode, freq,
                 endianess, IFACE_A, NULL, NULL);
    if (mpsse) {
      mpsse->description = supported_devices[i].description;
      return mpsse;
    }
  }

  return NULL;
}

/*
 * Open device by VID/PID
 *
 * @vid         - Device vendor ID.
 * @pid         - Device product ID.
 * @mode        - MPSSE mode, one of enum modes.
 * @freq        - Clock frequency to use for the specified mode.
 * @endianess   - Specifies how data is clocked in/out (MSB, LSB).
 * @interface   - FTDI interface to use (IFACE_A - IFACE_D).
 * @description - Device product description (set to NULL if not needed).
 * @serial      - Device serial number (set to NULL if not needed).
 *
 * Returns a pointer to an MPSSE context structure on success.
 */
struct mpsse_context* Open(int vid,
                           int pid,
                           enum modes mode,
                           int freq,
                           int endianess,
                           int interface,
                           const char* description,
                           const char* serial) {
  return OpenIndex(vid, pid, mode, freq, endianess, interface, description,
                   serial, 0);
}

/*
 * Open device by VID/PID/index
 *
 * @vid         - Device vendor ID.
 * @pid         - Device product ID.
 * @mode        - MPSSE mode, one of enum modes.
 * @freq        - Clock frequency to use for the specified mode.
 * @endianess   - Specifies how data is clocked in/out (MSB, LSB).
 * @interface   - FTDI interface to use (IFACE_A - IFACE_D).
 * @description - Device product description (set to NULL if not needed).
 * @serial      - Device serial number (set to NULL if not needed).
 * @index       - Device index (set to 0 if not needed).
 *
 * Returns a pointer to an MPSSE context structure.
 * On success, mpsse->open will be set to 1.
 * On failure, mpsse->open will be set to 0.
 */
struct mpsse_context* OpenIndex(int vid,
                                int pid,
                                enum modes mode,
                                int freq,
                                int endianess,
                                int interface,
                                const char* description,
                                const char* serial,
                                int index) {
  int status = 0;
  struct mpsse_context* mpsse = NULL;

  mpsse = malloc(sizeof(struct mpsse_context));
  if (!mpsse)
    return NULL;

  memset(mpsse, 0, sizeof(struct mpsse_context));

  /* Legacy; flushing is no longer needed, so disable it by default. */
  FlushAfterRead(mpsse, 0);

  /* ftdilib initialization */
  if (ftdi_init(&mpsse->ftdi)) {
    free(mpsse);
    return NULL;
  }

  /* Set the FTDI interface  */
  ftdi_set_interface(&mpsse->ftdi, interface);

  /* Open the specified device */
  if (!ftdi_usb_open_desc_index(&mpsse->ftdi, vid, pid, description, serial,
                                index)) {
    mpsse->mode = mode;
    mpsse->vid = vid;
    mpsse->pid = pid;
    mpsse->status = STOPPED;
    mpsse->endianess = endianess;

    /* Set the appropriate transfer size for the requested protocol */
    if (mpsse->mode == I2C)
      mpsse->xsize = I2C_TRANSFER_SIZE;
    else
      mpsse->xsize = SPI_RW_SIZE;

    status |= ftdi_usb_reset(&mpsse->ftdi);
    status |= ftdi_set_latency_timer(&mpsse->ftdi, LATENCY_MS);
    status |= ftdi_write_data_set_chunksize(&mpsse->ftdi, CHUNK_SIZE);
    status |= ftdi_read_data_set_chunksize(&mpsse->ftdi, CHUNK_SIZE);
    status |= ftdi_set_bitmode(&mpsse->ftdi, 0, BITMODE_RESET);

    if (status == 0) {
      /* Set the read and write timeout periods */
      set_timeouts(mpsse, USB_TIMEOUT);

      if (mpsse->mode != BITBANG) {
        ftdi_set_bitmode(&mpsse->ftdi, 0, BITMODE_MPSSE);

        if (SetClock(mpsse, freq) == MPSSE_OK) {
          if (SetMode(mpsse, endianess) == MPSSE_OK) {
            mpsse->opened = 1;

            /* Give the chip a few mS to initialize */
            usleep(SETUP_DELAY);

            /*
             * Not all FTDI chips support all the commands that SetMode may
             * have sent.
             * This clears out any errors from unsupported commands that
             * might have been sent during set up.
             */
            ftdi_usb_purge_buffers(&mpsse->ftdi);
          }
        }
      } else {
        /* Skip the setup functions if we're just operating in BITBANG mode
         */
        if (!ftdi_set_bitmode(&mpsse->ftdi, 0xFF, BITMODE_BITBANG))
          mpsse->opened = 1;
      }
    }
  }

  if (mpsse && !mpsse->opened) {
    Close(mpsse);
    mpsse = NULL;
  }

  return mpsse;
}

/*
 * Closes the device, deinitializes libftdi, and frees the MPSSE context
 *pointer.
 *
 * @mpsse - MPSSE context pointer.
 *
 * Returns void.
 */
void Close(struct mpsse_context* mpsse) {
  if (!mpsse)
    return;

  if (mpsse->opened) {
    /* Shut these down only if initialization succeeded before. */
    ftdi_set_bitmode(&mpsse->ftdi, 0, BITMODE_RESET);
    ftdi_usb_close(&mpsse->ftdi);
  }
  ftdi_deinit(&mpsse->ftdi);
  free(mpsse);
}

/* Enables bit-wise data transfers.
 * Must be called after MPSSE() / Open() / OpenIndex().
 *
 * Returns void.
 */
void EnableBitmode(struct mpsse_context* mpsse, int tf) {
  if (is_valid_context(mpsse)) {
    if (tf) {
      mpsse->tx |= MPSSE_BITMODE;
      mpsse->rx |= MPSSE_BITMODE;
      mpsse->txrx |= MPSSE_BITMODE;
    } else {
      mpsse->tx &= ~MPSSE_BITMODE;
      mpsse->rx &= ~MPSSE_BITMODE;
      mpsse->txrx &= ~MPSSE_BITMODE;
    }
  }
}

/*
 * Sets the appropriate transmit and receive commands based on the requested
 *mode and byte order.
 *
 * @mpsse     - MPSSE context pointer.
 * @endianess - MPSSE_MSB or MPSSE_LSB.
 *
 * Returns MPSSE_OK on success.
 * Returns MPSSE_FAIL on failure.
 */
int SetMode(struct mpsse_context* mpsse, int endianess) {
  int retval = MPSSE_OK, i = 0, setup_commands_size = 0;
  uint8_t buf[CMD_SIZE] = {0};
  uint8_t setup_commands[CMD_SIZE * MAX_SETUP_COMMANDS] = {0};

  /* Do not call is_valid_context() here, as the FTDI chip may not be completely
   * configured when SetMode is called */
  if (mpsse) {
    /* Read and write commands need to include endianess */
    mpsse->tx = MPSSE_DO_WRITE | endianess;
    mpsse->rx = MPSSE_DO_READ | endianess;
    mpsse->txrx = MPSSE_DO_WRITE | MPSSE_DO_READ | endianess;

    /* Clock, data out, chip select pins are outputs; all others are inputs. */
    mpsse->tris = DEFAULT_TRIS;

    /* Clock and chip select pins idle high; all others are low */
    mpsse->pidle = mpsse->pstart = mpsse->pstop = DEFAULT_PORT;

    /* During reads and writes the chip select pin is brought low */
    mpsse->pstart &= ~CS;

    /* Disable FTDI internal loopback */
    SetLoopback(mpsse, 0);

    /* Send ACKs by default */
    SetAck(mpsse, ACK);

    /* Ensure adaptive clock is disabled */
    setup_commands[setup_commands_size++] = DISABLE_ADAPTIVE_CLOCK;

    switch (mpsse->mode) {
      case SPI0:
        /* SPI mode 0 clock idles low */
        mpsse->pidle &= ~SK;
        mpsse->pstart &= ~SK;
        mpsse->pstop &= ~SK;
        /* SPI mode 0 propogates data on the falling edge and read data on the
         * rising edge of the clock */
        mpsse->tx |= MPSSE_WRITE_NEG;
        mpsse->rx &= ~MPSSE_READ_NEG;
        mpsse->txrx |= MPSSE_WRITE_NEG;
        mpsse->txrx &= ~MPSSE_READ_NEG;
        break;
      case SPI3:
        /* SPI mode 3 clock idles high */
        mpsse->pidle |= SK;
        mpsse->pstart |= SK;
        /* Keep the clock low while the CS pin is brought high to ensure we
         * don't accidentally clock out an extra bit */
        mpsse->pstop &= ~SK;
        /* SPI mode 3 propogates data on the falling edge and read data on the
         * rising edge of the clock */
        mpsse->tx |= MPSSE_WRITE_NEG;
        mpsse->rx &= ~MPSSE_READ_NEG;
        mpsse->txrx |= MPSSE_WRITE_NEG;
        mpsse->txrx &= ~MPSSE_READ_NEG;
        break;
      case SPI1:
        /* SPI mode 1 clock idles low */
        mpsse->pidle &= ~SK;
        /* Since this mode idles low, the start condition should ensure that the
         * clock is low */
        mpsse->pstart &= ~SK;
        /* Even though we idle low in this mode, we need to keep the clock line
         * high when we set the CS pin high to prevent
         * an unintended clock cycle from being sent by the FT2232. This way,
         * the clock goes high, but does not go low until
         * after the CS pin goes high.
         */
        mpsse->pstop |= SK;
        /* Data read on falling clock edge */
        mpsse->rx |= MPSSE_READ_NEG;
        mpsse->tx &= ~MPSSE_WRITE_NEG;
        mpsse->txrx |= MPSSE_READ_NEG;
        mpsse->txrx &= ~MPSSE_WRITE_NEG;
        break;
      case SPI2:
        /* SPI 2 clock idles high */
        mpsse->pidle |= SK;
        mpsse->pstart |= SK;
        mpsse->pstop |= SK;
        /* Data read on falling clock edge */
        mpsse->rx |= MPSSE_READ_NEG;
        mpsse->tx &= ~MPSSE_WRITE_NEG;
        mpsse->txrx |= MPSSE_READ_NEG;
        mpsse->txrx &= ~MPSSE_WRITE_NEG;
        break;
      case I2C:
        /* I2C propogates data on the falling clock edge and reads data on the
         * falling (or rising) clock edge */
        mpsse->tx |= MPSSE_WRITE_NEG;
        mpsse->rx &= ~MPSSE_READ_NEG;
        /* In I2C, both the clock and the data lines idle high */
        mpsse->pidle |= DO | DI;
        /* I2C start bit == data line goes from high to low while clock line is
         * high */
        mpsse->pstart &= ~DO & ~DI;
        /* I2C stop bit == data line goes from low to high while clock line is
         * high - set data line low here, so the transition to the idle state
         * triggers the stop condition. */
        mpsse->pstop &= ~DO & ~DI;
        /* Enable three phase clock to ensure that I2C data is available on both
         * the rising and falling clock edges */
        setup_commands[setup_commands_size++] = ENABLE_3_PHASE_CLOCK;
        break;
      case GPIO:
        break;
      default:
        retval = MPSSE_FAIL;
    }

    /* Send any setup commands to the chip */
    if (retval == MPSSE_OK && setup_commands_size > 0) {
      retval = raw_write(mpsse, setup_commands, setup_commands_size);
    }

    if (retval == MPSSE_OK) {
      /* Set the idle pin states */
      set_bits_low(mpsse, mpsse->pidle);

      /* All GPIO pins are outputs, set low */
      mpsse->trish = 0xFF;
      mpsse->gpioh = 0x00;

      buf[i++] = SET_BITS_HIGH;
      buf[i++] = mpsse->gpioh;
      buf[i++] = mpsse->trish;

      retval = raw_write(mpsse, buf, i);
    }
  } else {
    retval = MPSSE_FAIL;
  }

  return retval;
}

/*
 * Sets the appropriate divisor for the desired clock frequency.
 *
 * @mpsse - MPSSE context pointer.
 * @freq  - Desired clock frequency in hertz.
 *
 * Returns MPSSE_OK on success.
 * Returns MPSSE_FAIL on failure.
 */
int SetClock(struct mpsse_context* mpsse, uint32_t freq) {
  int retval = MPSSE_FAIL;
  uint32_t system_clock = 0;
  uint16_t divisor = 0;
  uint8_t buf[CMD_SIZE] = {0};

  /* Do not call is_valid_context() here, as the FTDI chip may not be completely
   * configured when SetClock is called */
  if (mpsse) {
    if (freq > SIX_MHZ) {
      buf[0] = TCK_X5;
      system_clock = SIXTY_MHZ;
    } else {
      buf[0] = TCK_D5;
      system_clock = TWELVE_MHZ;
    }

    if (raw_write(mpsse, buf, 1) == MPSSE_OK) {
      if (freq <= 0) {
        divisor = 0xFFFF;
      } else {
        divisor = freq2div(system_clock, freq);
      }

      buf[0] = TCK_DIVISOR;
      buf[1] = (divisor & 0xFF);
      buf[2] = ((divisor >> 8) & 0xFF);

      if (raw_write(mpsse, buf, 3) == MPSSE_OK) {
        mpsse->clock = div2freq(system_clock, divisor);
        retval = MPSSE_OK;
      }
    }
  }

  return retval;
}

/*
 * Retrieves the last error string from libftdi.
 *
 * @mpsse - MPSSE context pointer.
 *
 * Returns a pointer to the last error string.
 */
const char* ErrorString(struct mpsse_context* mpsse) {
  if (mpsse != NULL) {
    return ftdi_get_error_string(&mpsse->ftdi);
  }

  return NULL_CONTEXT_ERROR_MSG;
}

/*
 * Gets the currently configured clock rate.
 *
 * @mpsse - MPSSE context pointer.
 *
 * Returns the existing clock rate in hertz.
 */
int GetClock(struct mpsse_context* mpsse) {
  int clock = 0;

  if (is_valid_context(mpsse)) {
    clock = mpsse->clock;
  }

  return clock;
}

/*
 * Returns the vendor ID of the FTDI chip.
 *
 * @mpsse - MPSSE context pointer.
 *
 * Returns the integer value of the vendor ID.
 */
int GetVid(struct mpsse_context* mpsse) {
  int vid = 0;

  if (is_valid_context(mpsse)) {
    vid = mpsse->vid;
  }

  return vid;
}

/*
 * Returns the product ID of the FTDI chip.
 *
 * @mpsse - MPSSE context pointer.
 *
 * Returns the integer value of the product ID.
 */
int GetPid(struct mpsse_context* mpsse) {
  int pid = 0;

  if (is_valid_context(mpsse)) {
    pid = mpsse->pid;
  }

  return pid;
}

/*
 * Returns the description of the FTDI chip, if any.
 *
 * @mpsse - MPSSE context pointer.
 *
 * Returns the description of the FTDI chip.
 */
const char* GetDescription(struct mpsse_context* mpsse) {
  char* description = NULL;

  if (is_valid_context(mpsse)) {
    description = mpsse->description;
  }

  return description;
}

/*
 * Enable / disable internal loopback.
 *
 * @mpsse  - MPSSE context pointer.
 * @enable - Zero to disable loopback, 1 to enable loopback.
 *
 * Returns MPSSE_OK on success.
 * Returns MPSSE_FAIL on failure.
 */
int SetLoopback(struct mpsse_context* mpsse, int enable) {
  uint8_t buf[1] = {0};
  int retval = MPSSE_FAIL;

  if (is_valid_context(mpsse)) {
    if (enable) {
      buf[0] = LOOPBACK_START;
    } else {
      buf[0] = LOOPBACK_END;
    }

    retval = raw_write(mpsse, buf, 1);
  }

  return retval;
}

/*
 * Sets the idle state of the chip select pin. CS idles high by default.
 *
 * @mpsse - MPSSE context pointer.
 * @idle  - Set to 1 to idle high, 0 to idle low.
 *
 * Returns void.
 */
void SetCSIdle(struct mpsse_context* mpsse, int idle) {
  if (is_valid_context(mpsse)) {
    if (idle > 0) {
      /* Chip select idles high, active low */
      mpsse->pidle |= CS;
      mpsse->pstop |= CS;
      mpsse->pstart &= ~CS;
    } else {
      /* Chip select idles low, active high */
      mpsse->pidle &= ~CS;
      mpsse->pstop &= ~CS;
      mpsse->pstart |= CS;
    }
  }

  return;
}

/*
 * Enables or disables flushing of the FTDI chip's RX buffers after each read
 *operation.
 * Flushing is disable by default.
 *
 * @mpsse - MPSSE context pointer.
 * @tf    - Set to 1 to enable flushing, or 0 to disable flushing.
 *
 * Returns void.
 */
void FlushAfterRead(struct mpsse_context* mpsse, int tf) {
  mpsse->flush_after_read = tf;
  return;
}

/*
 * Send data start condition.
 *
 * @mpsse - MPSSE context pointer.
 *
 * Returns MPSSE_OK on success.
 * Returns MPSSE_FAIL on failure.
 */
int Start(struct mpsse_context* mpsse) {
  int status = MPSSE_OK;

  if (is_valid_context(mpsse)) {
    if (mpsse->mode == I2C && mpsse->status == STARTED) {
      /* Set the default pin states while the clock is low since this is an I2C
       * repeated start condition */
      status |= set_bits_low(mpsse, (mpsse->pidle & ~SK));

      /* Make sure the pins are in their default idle state */
      status |= set_bits_low(mpsse, mpsse->pidle);
    }

    /* Set the start condition */
    status |= set_bits_low(mpsse, mpsse->pstart);

    /*
     * Hackish work around to properly support SPI mode 3.
     * SPI3 clock idles high, but needs to be set low before sending out
     * data to prevent unintenteded clock glitches from the FT2232.
     */
    if (mpsse->mode == SPI3) {
      status |= set_bits_low(mpsse, (mpsse->pstart & ~SK));
    }
    /*
     * Hackish work around to properly support SPI mode 1.
     * SPI1 clock idles low, but needs to be set high before sending out
     * data to preven unintended clock glitches from the FT2232.
     */
    else if (mpsse->mode == SPI1) {
      status |= set_bits_low(mpsse, (mpsse->pstart | SK));
    }

    mpsse->status = STARTED;
  } else {
    status = MPSSE_FAIL;
    mpsse->status = STOPPED;
  }

  return status;
}

/*
 * Performs a bit-wise write of up to 8 bits at a time.
 *
 * @mpsse - MPSSE context pointer.
 * @bits  - A byte containing the desired bits to write.
 * @size  - The number of bits from the 'bits' byte to write.
 *
 * Returns MPSSE_OK on success, MPSSE_FAIL on failure.
 */
int WriteBits(struct mpsse_context* mpsse, char bits, size_t size) {
  uint8_t data[8] = {0};
  size_t i = 0;
  int retval = MPSSE_OK;

  if (size > sizeof(data)) {
    size = sizeof(data);
  }

  /* Convert each bit in bits to an array of bytes */
  for (i = 0; i < size; i++) {
    if (bits & (1 << i)) {
      /* Be sure to honor endianess */
      if (mpsse->endianess == LSB) {
        data[i] = '\xFF';
      } else {
        data[size - i - 1] = '\xFF';
      }
    }
  }

  /* Enable bit mode before writing, then disable it afterwards. */
  EnableBitmode(mpsse, 1);
  retval = Write(mpsse, data, size);
  EnableBitmode(mpsse, 0);

  return retval;
}

/*
 * Send data out via the selected serial protocol.
 *
 * @mpsse - MPSSE context pointer.
 * @data  - Buffer of data to send.
 * @size  - Size of data.
 *
 * Returns MPSSE_OK on success.
 * Returns MPSSE_FAIL on failure.
 */
int Write(struct mpsse_context* mpsse, const void* vdata, int size) {
  const uint8_t* data = vdata;
  uint8_t* buf = NULL;
  int retval = MPSSE_FAIL, buf_size = 0, txsize = 0, n = 0;

  if (is_valid_context(mpsse)) {
    if (mpsse->mode) {
      while (n < size) {
        txsize = size - n;
        if (txsize > mpsse->xsize) {
          txsize = mpsse->xsize;
        }

        /*
         * For I2C we need to send each byte individually so that we can
         * read back each individual ACK bit, so set the transmit size to 1.
         */
        if (mpsse->mode == I2C) {
          txsize = 1;
        }

        buf = build_block_buffer(mpsse, mpsse->tx, data + n, txsize, &buf_size);
        if (buf) {
          retval = raw_write(mpsse, buf, buf_size);
          n += txsize;
          free(buf);

          if (retval == MPSSE_FAIL) {
            break;
          }

          /* Read in the ACK bit and store it in mpsse->rack */
          if (mpsse->mode == I2C) {
            raw_read(mpsse, (uint8_t*)&mpsse->rack, 1);
          }
        } else {
          break;
        }
      }
    }

    if (retval == MPSSE_OK && n == size) {
      retval = MPSSE_OK;
    }
  }

  return retval;
}

/* Performs a read. For internal use only; see Read() and ReadBits(). */
static uint8_t* InternalRead(struct mpsse_context* mpsse, int size) {
  uint8_t *data = NULL, *buf = NULL;
  uint8_t sbuf[SPI_RW_SIZE] = {0};
  int n = 0, rxsize = 0, data_size = 0, retval = 0;

  if (is_valid_context(mpsse)) {
    if (mpsse->mode) {
      buf = malloc(size);
      if (buf) {
        memset(buf, 0, size);

        while (n < size) {
          rxsize = size - n;
          if (rxsize > mpsse->xsize) {
            rxsize = mpsse->xsize;
          }

          data = build_block_buffer(mpsse, mpsse->rx, sbuf, rxsize, &data_size);
          if (data) {
            retval = raw_write(mpsse, data, data_size);
            free(data);

            if (retval == MPSSE_OK) {
              n += raw_read(mpsse, buf + n, rxsize);
            } else {
              break;
            }
          } else {
            break;
          }
        }
      }
    }
  }

  return buf;
}

/*
 * Reads data over the selected serial protocol.
 *
 * @mpsse - MPSSE context pointer.
 * @size  - Number of bytes to read.
 *
 * Returns a pointer to the read data on success.
 * Returns NULL on failure.
 */
#ifdef SWIGPYTHON
swig_string_data Read(struct mpsse_context* mpsse, int size)
#else
uint8_t* Read(struct mpsse_context* mpsse, int size)
#endif
{
  uint8_t* buf = NULL;

  buf = InternalRead(mpsse, size);

#ifdef SWIGPYTHON
  swig_string_data sdata = {0};
  sdata.size = size;
  sdata.data = buf;
  return sdata;
#else
  return buf;
#endif
}

/*
 * Performs a bit-wise read of up to 8 bits.
 *
 * @mpsse - MPSSE context pointer.
 * @size  - Number of bits to read.
 *
 * Returns an 8-bit byte containing the read bits.
 */
char ReadBits(struct mpsse_context* mpsse, int size) {
  char bits = 0;
  uint8_t* rdata = NULL;

  if (size > 8) {
    size = 8;
  }

  EnableBitmode(mpsse, 1);
  rdata = InternalRead(mpsse, size);
  EnableBitmode(mpsse, 0);

  if (rdata) {
    /* The last byte in rdata will have all the read bits set or unset as
     * needed. */
    bits = rdata[size - 1];

    if (mpsse->endianess == MSB) {
      /*
       * In MSB mode, bits are sifted in from the left. If less than 8 bits were
       * read, we need to shift them left accordingly.
       */
      bits = bits << (8 - size);
    } else if (mpsse->endianess == LSB) {
      /*
       * In LSB mode, bits are shifted in from the right. If less than 8 bits
       * were
       * read, we need to shift them right accordingly.
       */
      bits = bits >> (8 - size);
    }

    free(rdata);
  }

  return bits;
}

/*
 * Reads and writes data over the selected serial protocol (SPI only).
 *
 * @mpsse - MPSSE context pointer.
 * @data  - Buffer containing bytes to write.
 * @size  - Number of bytes to transfer.
 *
 * Returns a pointer to the read data on success.
 * Returns NULL on failure.
 */
#ifdef SWIGPYTHON
swig_string_data Transfer(struct mpsse_context* mpsse, char* data, int size)
#else
uint8_t* Transfer(struct mpsse_context* mpsse, uint8_t* data, int size)
#endif
{
  uint8_t *txdata = NULL, *buf = NULL;
  int n = 0, data_size = 0, rxsize = 0, retval = 0;

  if (is_valid_context(mpsse)) {
    /* Make sure we're configured for one of the SPI modes */
    if (mpsse->mode >= SPI0 && mpsse->mode <= SPI3) {
      buf = malloc(size);
      if (buf) {
        memset(buf, 0, size);

        while (n < size) {
          /* When sending and recieving, FTDI chips don't seem to like large
           * data blocks. Limit the size of each block to SPI_TRANSFER_SIZE */
          rxsize = size - n;
          if (rxsize > SPI_TRANSFER_SIZE) {
            rxsize = SPI_TRANSFER_SIZE;
          }

          txdata = build_block_buffer(mpsse, mpsse->txrx, data + n, rxsize,
                                      &data_size);
          if (txdata) {
            retval = raw_write(mpsse, txdata, data_size);
            free(txdata);

            if (retval == MPSSE_OK) {
              n += raw_read(mpsse, (buf + n), rxsize);
            } else {
              break;
            }
          } else {
            break;
          }
        }
      }
    }
  }

#ifdef SWIGPYTHON
  swig_string_data sdata = {0};
  sdata.size = n;
  sdata.data = (char*)buf;
  return sdata;
#else
  return buf;
#endif
}

/*
 * Returns the last received ACK bit.
 *
 * @mpsse - MPSSE context pointer.
 *
 * Returns either an ACK (0) or a NACK (1).
 */
int GetAck(struct mpsse_context* mpsse) {
  int ack = 0;

  if (is_valid_context(mpsse)) {
    ack = (mpsse->rack & 0x01);
  }

  return ack;
}

/*
 * Sets the transmitted ACK bit.
 *
 * @mpsse - MPSSE context pointer.
 * @ack   - 0 to send ACKs, 1 to send NACKs.
 *
 * Returns void.
 */
void SetAck(struct mpsse_context* mpsse, int ack) {
  if (is_valid_context(mpsse)) {
    if (ack == NACK) {
      mpsse->tack = 0xFF;
    } else {
      mpsse->tack = 0x00;
    }
  }

  return;
}

/*
 * Causes libmpsse to send ACKs after each read byte in I2C mode.
 *
 * @mpsse - MPSSE context pointer.
 *
 * Returns void.
 */
void SendAcks(struct mpsse_context* mpsse) {
  return SetAck(mpsse, ACK);
}

/*
 * Causes libmpsse to send NACKs after each read byte in I2C mode.
 *
 * @mpsse - MPSSE context pointer.
 *
 * Returns void.
 */
void SendNacks(struct mpsse_context* mpsse) {
  return SetAck(mpsse, NACK);
}

/*
 * Send data stop condition.
 *
 * @mpsse - MPSSE context pointer.
 *
 * Returns MPSSE_OK on success.
 * Returns MPSSE_FAIL on failure.
 */
int Stop(struct mpsse_context* mpsse) {
  int retval = MPSSE_OK;

  if (is_valid_context(mpsse)) {
    /* In I2C mode, we need to ensure that the data line goes low while the
     * clock line is low to avoid sending an inadvertent start condition */
    if (mpsse->mode == I2C) {
      retval |= set_bits_low(mpsse, (mpsse->pidle & ~DO & ~SK));
    }

    /* Send the stop condition */
    retval |= set_bits_low(mpsse, mpsse->pstop);

    if (retval == MPSSE_OK) {
      /* Restore the pins to their idle states */
      retval |= set_bits_low(mpsse, mpsse->pidle);
    }

    mpsse->status = STOPPED;
  } else {
    retval = MPSSE_FAIL;
    mpsse->status = STOPPED;
  }

  return retval;
}

/*
 * Sets the specified pin high.
 *
 * @mpsse - MPSSE context pointer.
 * @pin   - Pin number to set high.
 *
 * Returns MPSSE_OK on success.
 * Returns MPSSE_FAIL on failure.
 */
int PinHigh(struct mpsse_context* mpsse, int pin) {
  int retval = MPSSE_FAIL;

  if (is_valid_context(mpsse)) {
    retval = gpio_write(mpsse, pin, HIGH);
  }

  return retval;
}

/*
 * Sets the specified pin low.
 *
 * @mpsse - MPSSE context pointer.
 * @pin   - Pin number to set low.
 *
 * Returns MPSSE_OK on success.
 * Returns MPSSE_FAIL on failure.
 */
int PinLow(struct mpsse_context* mpsse, int pin) {
  int retval = MPSSE_FAIL;

  if (is_valid_context(mpsse)) {
    retval = gpio_write(mpsse, pin, LOW);
  }

  return retval;
}

/*
 * Sets the input/output direction of all pins. For use in BITBANG mode only.
 *
 * @mpsse     - MPSSE context pointer.
 * @direction - Byte indicating input/output direction of each bit.  1 is out.
 *
 * Returns MPSSE_OK if direction could be set, MPSSE_FAIL otherwise.
 */
int SetDirection(struct mpsse_context* mpsse, uint8_t direction) {
  int retval = MPSSE_FAIL;

  if (is_valid_context(mpsse)) {
    if (mpsse->mode == BITBANG) {
      if (ftdi_set_bitmode(&mpsse->ftdi, direction, BITMODE_BITBANG) == 0) {
        retval = MPSSE_OK;
      }
    }
  }

  return retval;
}

/*
 * Sets the input/output value of all pins. For use in BITBANG mode only.
 *
 * @mpsse - MPSSE context pointer.
 * @data  - Byte indicating bit hi/low value of each bit.
 *
 * Returns MPSSE_OK if direction could be set, MPSSE_FAIL otherwise.
 */
int WritePins(struct mpsse_context* mpsse, uint8_t data) {
  int retval = MPSSE_FAIL;

  if (is_valid_context(mpsse)) {
    if (mpsse->mode == BITBANG) {
      if (ftdi_write_data(&mpsse->ftdi, &data, 1) == 0) {
        retval = MPSSE_OK;
      }
    }
  }

  return retval;
}

/*
 * Reads the state of the chip's pins. For use in BITBANG mode only.
 *
 * @mpsse - MPSSE context pointer.
 *
 * Returns a byte with the corresponding pin's bits set to 1 or 0.
 */
int ReadPins(struct mpsse_context* mpsse) {
  uint8_t val = 0;

  if (is_valid_context(mpsse)) {
    ftdi_read_pins((struct ftdi_context*)&mpsse->ftdi, (uint8_t*)&val);
  }

  return (int)val;
}

/*
 * Checks if a specific pin is high or low. For use in BITBANG mode only.
 *
 * @mpsse - MPSSE context pointer.
 * @pin   - The pin number.
 * @state - The state of the pins, as returned by ReadPins.
 *          If set to -1, ReadPins will automatically be called.
 *
 * Returns a 1 if the pin is high, 0 if the pin is low.
 */
int PinState(struct mpsse_context* mpsse, int pin, int state) {
  if (state == -1) {
    state = ReadPins(mpsse);
  }

  /* If not in bitbang mode, the specified pin should be one of GPIOLx. Convert
   * these defines into an absolute pin number. */
  if (mpsse->mode != BITBANG) {
    pin += NUM_GPIOL_PINS;
  }

  return ((state & (1 << pin)) >> pin);
}

/*
 * Places all I/O pins into a tristate mode.
 *
 * @mpsse - MPSSE context pointer.
 *
 * Returns MPSSE_OK on success, MPSSE_FAIL on failure.
 */
int Tristate(struct mpsse_context* mpsse) {
  uint8_t cmd[CMD_SIZE] = {0};

  /* Tristate the all I/O pins (FT232H only) */
  cmd[0] = TRISTATE_IO;
  cmd[1] = 0xFF;
  cmd[2] = 0xFF;

  return raw_write(mpsse, cmd, sizeof(cmd));
}
