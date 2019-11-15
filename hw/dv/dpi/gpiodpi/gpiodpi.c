// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "gpiodpi.h"

#ifdef __linux__
#include <pty.h>
#elif __APPLE__
#include <util.h>
#endif

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

// This file does a lot of bit setting and getting; these macros are intended to
// make that a little more readable.
#define GET_BIT(word, bit_idx) (((word) >> (bit_idx)) & 1)
#define SET_BIT(word, bit_idx) ((word) |= (1 << (bit_idx)))
#define CLR_BIT(word, bit_idx) ((word) &= ~(1 << (bit_idx)))

struct gpiodpi_ctx {
  // The number of pins we're driving.
  int n_bits;

  // The last known value of the pins, in little-endian order.
  uint32_t driven_pin_values;

  // File descriptors and paths for the device-to-host and host-to-device
  // FIFOs.
  int dev_to_host_fifo;
  char dev_to_host_path[PATH_MAX];
  int host_to_dev_fifo;
  char host_to_dev_path[PATH_MAX];
};

/**
 * Creates a new UNIX FIFO file at |path_buf|, and opens it with |flags|.
 *
 * @return a file descriptor for the FIFO, or -1 if any syscall failed.
 */
static int open_fifo(char *path_buf, int flags) {
  int fifo_status = mkfifo(path_buf, 0644);
  if (fifo_status != 0) {
    if (errno == EEXIST) {
      fprintf(stderr, "GPIO: Reusing existing FIFO at %s\n", path_buf);
    } else {
      fprintf(stderr, "GPIO: Unable to create FIFO at %s: %s\n", path_buf,
              strerror(errno));
      return -1;
    }
  }

  int fd = open(path_buf, flags);
  if (fd < 0) {
    // Delete the fifo we created; ignore errors.
    unlink(path_buf);
    fprintf(stderr, "GPIO: Unable to open FIFO at %s: %s\n", path_buf,
            strerror(errno));
    return -1;
  }

  return fd;
}

/**
 * Print out a usage message for the GPIO interface.
 *
 * @arg rfifo the path to the "read" side (w.r.t the host).
 * @arg wfifo the path to the "write" side (w.r.t the host).
 * @arg n_bits the number of pins supported.
 */
static void print_usage(char *rfifo, char *wfifo, int n_bits) {
  printf("\n");
  printf(
      "GPIO: FIFO pipes created at %s (read) and %s (write) for %d-bit wide "
      "GPIO.\n",
      rfifo, wfifo, n_bits);
  printf(
      "GPIO: To measure the values of the pins as driven by the device, run\n");
  printf("$ cat %s  # '0' low, '1' high, 'X' floating\n", rfifo);
  printf("GPIO: To drive the pins, run a command like\n");
  printf("$ echo 'h09 l31' > %s  # Pull the pin 9 high, and pin 31 low.\n",
         wfifo);
}

void *gpiodpi_create(const char *name, int n_bits) {
  struct gpiodpi_ctx *ctx =
      (struct gpiodpi_ctx *)malloc(sizeof(struct gpiodpi_ctx));
  assert(ctx);

  // n_bits > 32 requires more sophisticated handling of svBitVecVal which we
  // currently don't do.
  assert(n_bits <= 32 && "n_bits must be <= 32");
  ctx->n_bits = n_bits;

  ctx->driven_pin_values = 0;

  char cwd_buf[PATH_MAX];
  char *cwd = getcwd(cwd_buf, sizeof(cwd_buf));
  assert(cwd != NULL);

  int path_len;
  path_len = snprintf(ctx->dev_to_host_path, PATH_MAX, "%s/%s-read", cwd, name);
  assert(path_len > 0 && path_len <= PATH_MAX);
  path_len =
      snprintf(ctx->host_to_dev_path, PATH_MAX, "%s/%s-write", cwd, name);
  assert(path_len > 0 && path_len <= PATH_MAX);

  ctx->dev_to_host_fifo = open_fifo(ctx->dev_to_host_path, O_RDWR);
  if (ctx->dev_to_host_fifo < 0) {
    return NULL;
  }

  ctx->host_to_dev_fifo = open_fifo(ctx->host_to_dev_path, O_RDWR);
  if (ctx->host_to_dev_fifo < 0) {
    return NULL;
  }

  int flags = fcntl(ctx->host_to_dev_fifo, F_GETFL, 0);
  fcntl(ctx->host_to_dev_fifo, F_SETFL, flags | O_NONBLOCK);

  print_usage(ctx->dev_to_host_path, ctx->host_to_dev_path, ctx->n_bits);

  return (void *)ctx;
}

void gpiodpi_device_to_host(void *ctx_void, svBitVecVal *gpio_data,
                            svBitVecVal *gpio_oe) {
  struct gpiodpi_ctx *ctx = (struct gpiodpi_ctx *)ctx_void;
  assert(ctx);

  // Write 0, 1, or X (when oe is not set) for each GPIO pin, in big endian
  // order (i.e., pin 0 is the last character written). Finish it with a
  // newline.
  char gpio_str[32 + 1];
  char *pin_char = gpio_str;
  for (int i = ctx->n_bits - 1; i >= 0; --i, ++pin_char) {
    if (!GET_BIT(gpio_oe[0], i)) {
      *pin_char = 'X';
    } else if (GET_BIT(gpio_data[0], i)) {
      *pin_char = '1';
    } else {
      *pin_char = '0';
    }
  }
  *pin_char = '\n';

  ssize_t written = write(ctx->dev_to_host_fifo, gpio_str, ctx->n_bits + 1);
  assert(written == ctx->n_bits + 1);
}

/**
 * Parses an unsigned decimal number from |text|, advancing it forward as
 * necessary.
 *
 * Returns upon encountering any non-decimal digit.
 */
static uint32_t parse_dec(char **text) {
  if (text == NULL || *text == NULL) {
    return 0;
  }

  uint32_t value = 0;
  for (; **text != '\0'; ++*text) {
    char c = **text;
    uint32_t digit;
    if (c >= '0' && c <= '9') {
      digit = (c - '0');
    } else {
      break;
    }

    value *= 10;
    value += digit;
  }

  return value;
}

uint32_t gpiodpi_host_to_device_tick(void *ctx_void, svBitVecVal *gpio_oe) {
  struct gpiodpi_ctx *ctx = (struct gpiodpi_ctx *)ctx_void;
  assert(ctx);

  char gpio_str[32 + 2];
  ssize_t read_len = read(ctx->host_to_dev_fifo, gpio_str, 32 + 1);
  if (read_len < 0) {
    return ctx->driven_pin_values;
  }
  gpio_str[read_len] = '\0';

  char *gpio_text = gpio_str;
  for (; *gpio_text != '\0'; ++gpio_text) {
    switch (*gpio_text) {
      case '\n':
      case '\r':
      case '\0':
        goto parse_loop_end;
      case 'l':
      case 'L': {
        ++gpio_text;
        int idx = parse_dec(&gpio_text);
        if (!GET_BIT(gpio_oe[0], idx)) {
          fprintf(stderr,
                  "GPIO: Host tried to pull disabled pin low: pin %2d\n", idx);
        }
        CLR_BIT(ctx->driven_pin_values, idx);
        break;
      }
      case 'h':
      case 'H': {
        ++gpio_text;
        int idx = parse_dec(&gpio_text);
        if (!GET_BIT(gpio_oe[0], idx)) {
          fprintf(stderr,
                  "GPIO: Host tried to pull disabled pin high: pin %2d\n", idx);
        }
        SET_BIT(ctx->driven_pin_values, idx);
        break;
      }
      default:
        break;
    }
  }

parse_loop_end:
  return ctx->driven_pin_values;
}

void gpiodpi_close(void *ctx_void) {
  struct gpiodpi_ctx *ctx = (struct gpiodpi_ctx *)ctx_void;
  if (ctx == NULL) {
    return;
  }

  if (close(ctx->dev_to_host_fifo) != 0) {
    printf("GPIO: Failed to close FIFO file at %s: %s\n", ctx->dev_to_host_path,
           strerror(errno));
  }
  if (close(ctx->host_to_dev_fifo) != 0) {
    printf("GPIO: Failed to close FIFO file at %s: %s\n", ctx->host_to_dev_path,
           strerror(errno));
  }

  if (unlink(ctx->dev_to_host_path) != 0) {
    printf("GPIO: Failed to unlink FIFO file at %s: %s\n",
           ctx->dev_to_host_path, strerror(errno));
  }
  if (unlink(ctx->host_to_dev_path) != 0) {
    printf("GPIO: Failed to unlink FIFO file at %s: %s\n",
           ctx->host_to_dev_path, strerror(errno));
  }

  free(ctx);
}
