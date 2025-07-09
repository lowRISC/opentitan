// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The code below uses cfmakeraw, which comes from unistd.h. With glibc, it is
// only provided if the _DEFAULT_SOURCE feature test macro is defined (because
// it came from BSD in the first place, so needs pulling in explicitly).
#define _DEFAULT_SOURCE

#include "uartdpi.h"

#ifdef __linux__
#include <pty.h>
#elif __APPLE__
#include <util.h>
#endif

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define EXIT_STRING_MAX_LENGTH (64)

// This keeps the necessary uart state.
struct uartdpi_ctx {
  char ptyname[64];
  char exitstring[EXIT_STRING_MAX_LENGTH];
  int exittracker;
  int host;
  int device;
  char tmp_read;
  FILE *log_file;
};

void *uartdpi_create(const char *name, const char *log_file_path,
                     const char *exit_string) {
  struct uartdpi_ctx *ctx =
      (struct uartdpi_ctx *)malloc(sizeof(struct uartdpi_ctx));
  assert(ctx);

  int rv;

  // Initialize UART pseudo-terminal
  rv = openpty(&ctx->host, &ctx->device, 0, 0, 0);
  assert(rv == 0 && "failed to open pty for uart");

  // Customise the slave side of the uart pseudo-terminal to be in "raw mode",
  // using the BSD cfmakeraw function.
  struct termios tty;
  rv = tcgetattr(ctx->device, &tty);
  assert(rv == 0 && "failed to get device terminal attrs");
  cfmakeraw(&tty);
  rv = tcsetattr(ctx->device, TCSANOW, &tty);
  assert(rv == 0 && "failed to set new device terminal attrs");

  rv = ttyname_r(ctx->device, ctx->ptyname, 64);
  assert(rv == 0 && "ttyname_r failed");

  int cur_flags = fcntl(ctx->host, F_GETFL, 0);
  assert(cur_flags != -1 && "Unable to read current flags.");
  int new_flags = fcntl(ctx->host, F_SETFL, cur_flags | O_NONBLOCK);
  assert(new_flags != -1 && "Unable to set FD flags");

  printf(
      "\n"
      "UART: Created %s for %s. Connect to it with any terminal program, e.g.\n"
      "$ screen %s\n",
      ctx->ptyname, name, ctx->ptyname);

  // Open log file (if requested)
  ctx->log_file = NULL;
  bool write_log_file = strlen(log_file_path) != 0;
  if (write_log_file) {
    if (strcmp(log_file_path, "-") == 0) {
      ctx->log_file = stdout;
      printf("UART: Additionally writing all UART output to STDOUT.\n");

    } else {
      FILE *log_file;
      log_file = fopen(log_file_path, "w");
      if (!log_file) {
        fprintf(stderr, "UART: Unable to open log file at %s: %s\n",
                log_file_path, strerror(errno));
      } else {
        // Switch log file output to line buffering to ensure lines written to
        // the UART device show up in the log file as soon as a newline
        // character is written.
        rv = setvbuf(log_file, NULL, _IOLBF, 0);
        assert(rv == 0);

        ctx->log_file = log_file;
        printf("UART: Additionally writing all UART output to '%s'.\n",
               log_file_path);
      }
    }
  }

  ctx->exittracker = 0;
  if (strnlen(exit_string, EXIT_STRING_MAX_LENGTH) < EXIT_STRING_MAX_LENGTH) {
    strncpy(ctx->exitstring, exit_string, EXIT_STRING_MAX_LENGTH);
  } else {
    fprintf(stderr,
            "UART: Unable to copy exit string since its length is larger "
            "than the maximum %d.\n",
            EXIT_STRING_MAX_LENGTH);
    // Initialise as a null string.
    ctx->exitstring[0] = '\0';
  }
  // Guarantee that at least one character in the exit string is null.
  ctx->exitstring[EXIT_STRING_MAX_LENGTH - 1] = '\0';

  return (void *)ctx;
}

void uartdpi_close(void *ctx_void) {
  struct uartdpi_ctx *ctx = (struct uartdpi_ctx *)ctx_void;
  if (!ctx) {
    return;
  }

  close(ctx->host);
  close(ctx->device);

  if (ctx->log_file) {
    // Always ensure the log file is flushed (most important when writing
    // to STDOUT)
    fflush(ctx->log_file);
    if (ctx->log_file != stdout) {
      fclose(ctx->log_file);
    }
  }

  free(ctx);
}

int uartdpi_can_read(void *ctx_void) {
  struct uartdpi_ctx *ctx = (struct uartdpi_ctx *)ctx_void;
  if (ctx == NULL) {
    return 0;
  }
  int rv = read(ctx->host, &ctx->tmp_read, 1);
  return (rv == 1);
}

char uartdpi_read(void *ctx_void) {
  struct uartdpi_ctx *ctx = (struct uartdpi_ctx *)ctx_void;

  return ctx->tmp_read;
}

int uartdpi_write(void *ctx_void, char c) {
  int rv;
  struct uartdpi_ctx *ctx = (struct uartdpi_ctx *)ctx_void;
  if (ctx == NULL) {
    return 0;
  }

  rv = write(ctx->host, &c, 1);
  assert(rv == 1 && "Write to pseudo-terminal failed.");

  if (ctx->log_file) {
    rv = fwrite(&c, sizeof(char), 1, ctx->log_file);
    assert(rv == 1 && "Write to log file failed.");
  }

  if (c == '\0') {
    // If a null character is received the tracker is reset.
    ctx->exittracker = 0;
  } else {
    // If it is not null compare with the exit string.
    if (c == ctx->exitstring[ctx->exittracker]) {
      // Track which character should match next.
      ctx->exittracker++;
    } else {
      // If the failing character matches the first character of the exit string
      // the tracker should be one.
      if (c == ctx->exitstring[0]) {
        ctx->exittracker = 1;
      } else {
        // Otherwise keep looking for the first character.
        ctx->exittracker = 0;
      }
    }
  }

  // If we hit the max length or the next character in the exit string is null.
  if (ctx->exittracker == EXIT_STRING_MAX_LENGTH ||
      ctx->exitstring[ctx->exittracker] == '\0') {
    // If exittracker is zero, exitstring is empty so we should not exit the
    // simulator.
    rv = ctx->exittracker;
    ctx->exittracker = 0;
    return rv;
  }

  return 0;
}
