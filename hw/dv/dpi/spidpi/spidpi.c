// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "spidpi.h"

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

#include "tcp_server.h"
#include "verilator_sim_ctrl.h"

// Enable this define to stop tracing at cycle 4
// and resume at the first SPI packet
// #define CONTROL_TRACE

struct spidpi_ctx {
  int loglevel;
  // Server context
  struct tcp_server_ctx *sock;
  char ptyname[64];
  int host;
  int device;
  FILE *mon_file;
  char mon_pathname[PATH_MAX];
  void *mon;
  int tick;
  int cpol;
  int cpha;
  int msbfirst;  // shift direction
  int nout;
  int bout;
  int nin;
  int bin;
  int din;
  int nmax;
  char driving;
  int state;
  int delay;
  char buf[MAX_TRANSFER];

  bool xfer_start;
  bool xfer_finish;
  bool xfer_read;
  bool xfer_write;
  int xfer_max;
  int xfer_indent;
  int xfer_count;
  const char *xfer_next;
  char xfer_buf_in[MAX_TRANSACTION];
  char xfer_buf_out[MAX_TRANSACTION];
};

static const char *json_find_next_char(char value, const char *ptr) {
  const char *tmp_ptr = ptr;

  while (tmp_ptr != NULL && *tmp_ptr != value && *tmp_ptr != ']' &&
         *tmp_ptr != '\0')
    tmp_ptr++;

  // Exit conditions
  if (tmp_ptr == NULL || *tmp_ptr == ']' || *tmp_ptr == '\0')
    tmp_ptr = NULL;

  return tmp_ptr;
}

static const char *json_parse_next_tag(char *tag, int tag_size,
                                       const char *ptr) {
  const char *tmp_ptr = ptr;

  tmp_ptr = json_find_next_char('"', tmp_ptr);
  if (tmp_ptr != NULL)
    tmp_ptr++;

  int index = 0;
  while (index < (tag_size - 1) && tmp_ptr != NULL && *tmp_ptr != '"' &&
         *tmp_ptr != ']' && *tmp_ptr != '\0') {
    tag[index++] = *tmp_ptr++;
  }
  tag[index] = '\0';

  // Exit conditions
  if (tmp_ptr == NULL || *tmp_ptr == ']' || *tmp_ptr == '\0')
    tmp_ptr = NULL;

  return tmp_ptr;
}

static const char *json_parse_next_integer(int *val, const char *ptr) {
  const char *tmp_ptr = ptr;
  char digits[32];

  while (tmp_ptr != NULL && isspace(*tmp_ptr))
    tmp_ptr++;

  int index = 0;
  while (index < (sizeof(digits) - 1) && tmp_ptr != NULL &&
         (isdigit(*tmp_ptr) || *tmp_ptr == '+' || *tmp_ptr == '-')) {
    digits[index++] = *tmp_ptr++;
  }
  digits[index] = '\0';
  if (val != NULL) {
    *val = atoi(digits);
  }

  // Exit conditions
  if (tmp_ptr == NULL || *tmp_ptr == ']' || *tmp_ptr == '\0')
    tmp_ptr = NULL;

  return tmp_ptr;
}

static const char *json_parse_next_integer_array(char *vals, int *num_vals,
                                                 const char *ptr) {
  const char *tmp_ptr = ptr;
  char digits[32];
  int max_values = INT_MAX;

  if (num_vals != NULL) {
    max_values = *num_vals ? *num_vals : INT_MAX;
    *num_vals = 0;
  }

  tmp_ptr = json_find_next_char('[', tmp_ptr);
  if (tmp_ptr != NULL)
    tmp_ptr++;

  while (tmp_ptr != NULL && *tmp_ptr != ']') {
    while (isspace(*tmp_ptr))
      tmp_ptr++;

    int index = 0;
    while (index < (sizeof(digits) - 1) &&
           (isdigit(*tmp_ptr) || *tmp_ptr == '+' || *tmp_ptr == '-')) {
      digits[index++] = *tmp_ptr++;
    }
    digits[index] = '\0';
    if (vals != NULL && num_vals != NULL && max_values > *num_vals) {
      vals[(*num_vals)++] = atoi(digits);
    }

    while (isspace(*tmp_ptr))
      tmp_ptr++;
    if (*tmp_ptr == ',')
      tmp_ptr++;
    if (*tmp_ptr == '\0')
      tmp_ptr = NULL;
  }
  // Exit conditions
  if (tmp_ptr != NULL && *tmp_ptr == ']')
    tmp_ptr++;
  if (tmp_ptr == NULL || *tmp_ptr == ']' || *tmp_ptr == '\0')
    tmp_ptr = NULL;

  return tmp_ptr;
}

static const char *xfer_parse_next_trans(void *ctx_void, const char *xfer_ptr) {
  struct spidpi_ctx *ctx = (struct spidpi_ctx *)ctx_void;
  const char *trans_ptr = xfer_ptr;
  char tag[16];

  // find next transaction
  trans_ptr = json_find_next_char('{', trans_ptr);

  // parse next transaction type (Write/Read/Both)
  trans_ptr = json_parse_next_tag(tag, sizeof(tag), trans_ptr);

  trans_ptr = json_find_next_char(':', trans_ptr);

  if (trans_ptr == NULL) {
    return trans_ptr;
  }

  memset(ctx->buf, 0x0, sizeof(ctx->buf));
  ctx->xfer_read = false;
  ctx->xfer_write = false;

  if (strstr(tag, "Write") != NULL) {
    trans_ptr = json_find_next_char('{', trans_ptr);
    trans_ptr = json_parse_next_tag(tag, sizeof(tag), trans_ptr);
    if (strstr(tag, "data") != NULL) {
      trans_ptr = json_find_next_char(':', trans_ptr);
      if (trans_ptr != NULL) {
        int data_size = sizeof(ctx->buf);
        trans_ptr++;
        trans_ptr =
            json_parse_next_integer_array(ctx->buf, &data_size, trans_ptr);
        ctx->xfer_write = true;
        ctx->nmax = data_size;
      }
    }
    trans_ptr = json_find_next_char('}', trans_ptr);
  } else if (strstr(tag, "Read") != NULL) {
    trans_ptr = json_find_next_char('{', trans_ptr);
    trans_ptr = json_parse_next_tag(tag, sizeof(tag), trans_ptr);
    if (strstr(tag, "len") != NULL) {
      trans_ptr = json_find_next_char(':', trans_ptr);
      if (trans_ptr != NULL) {
        int data_size;
        trans_ptr++;
        trans_ptr = json_parse_next_integer(&data_size, trans_ptr);
        ctx->xfer_read = true;
        ctx->nmax = data_size;
      }
    }
    trans_ptr = json_find_next_char('}', trans_ptr);
  } else if (strstr(tag, "Both") != NULL) {
    assert(false && "Both transaction not supported.");
  }

  if (trans_ptr != NULL)
    trans_ptr++;
  trans_ptr = json_find_next_char('}', trans_ptr);

  return trans_ptr;
}

static bool xfer_parse(void *ctx_void) {
  struct spidpi_ctx *ctx = (struct spidpi_ctx *)ctx_void;

  ctx->xfer_start = false;
  ctx->xfer_finish = false;
  ctx->xfer_buf_in[ctx->xfer_count] = '\0';
  ctx->xfer_next = NULL;

  // Simple parser of SPI JSON transaction header
  char *ptr = ctx->xfer_buf_in;
  if ((ptr = strstr(ptr, "Req")) != NULL &&
      (ptr = strstr(ptr, "Spi")) != NULL && (ptr = strstr(ptr, "id")) != NULL &&
      (ptr = strstr(ptr, "command")) != NULL &&
      (ptr = strstr(ptr, "RunTransaction")) != NULL &&
      (ptr = strstr(ptr, "transaction")) != NULL &&
      (ptr = strstr(ptr, "[")) != NULL) {
    if ((ctx->xfer_next = xfer_parse_next_trans(ctx, ptr)) != NULL) {
      return true;
    }
  }

  return false;
}

static void xfer_respond_next_trans(void *ctx_void) {
  struct spidpi_ctx *ctx = (struct spidpi_ctx *)ctx_void;

  // assemble SPI JSON response
  if (!ctx->xfer_start) {
    sprintf(ctx->xfer_buf_out,
            "{\"Res\":{\"Ok\":{"
            "\"Spi\":{\"RunTransaction\":{\"transaction\":[");
    ctx->xfer_start = true;
  } else {
    strcat(ctx->xfer_buf_out, ",");
  }

  if (ctx->xfer_write && ctx->xfer_read) {
    assert(false && "Response to Both transaction not supported.");
  } else if (ctx->xfer_write) {
    strcat(ctx->xfer_buf_out, "\"Write\"");
  } else if (ctx->xfer_read) {
    char value[16];

    strcat(ctx->xfer_buf_out, "{\"Read\":{\"data\":[");
    if (ctx->nmax > 0) {
      for (int i = 0; i < (ctx->nmax - 1); i++) {
        sprintf(value, "%u,", (uint8_t)ctx->buf[i]);
        strcat(ctx->xfer_buf_out, value);
      }
      sprintf(value, "%u", (uint8_t)ctx->buf[ctx->nmax - 1]);
      strcat(ctx->xfer_buf_out, value);
    }
    strcat(ctx->xfer_buf_out, "]}}");
  } else {
    assert(false && "Response to No transaction not supported.");
  }
}

static void xfer_respond(void *ctx_void, bool error) {
  struct spidpi_ctx *ctx = (struct spidpi_ctx *)ctx_void;

  if (error) {
    sprintf(ctx->xfer_buf_out,
            "{\"Res\":{\"Err\":{"
            "\"description\":\"Error processing SPI device transaction\","
            "\"backtrace\":\"%s:%d\""
            "}}}\n",
            __FILE__, __LINE__);
  } else {
    strcat(ctx->xfer_buf_out, "]}}}}}\n");
  }

  int count = strlen(ctx->xfer_buf_out);

  if (ctx->sock) {
    for (int i = 0; i < count; i++) {
      tcp_server_write(ctx->sock, ctx->xfer_buf_out[i]);
    }
  } else {
    int rv = write(ctx->host, ctx->xfer_buf_out, count);
    assert(rv == count && "write() failed.");
  }
}

static void xfer_reset(void *ctx_void) {
  struct spidpi_ctx *ctx = (struct spidpi_ctx *)ctx_void;

  ctx->xfer_start = false;
  ctx->xfer_finish = false;
  ctx->xfer_read = false;
  ctx->xfer_write = false;
  ctx->xfer_max = MAX_TRANSACTION;
  ctx->xfer_indent = 0;
  ctx->xfer_next = NULL;
  ctx->xfer_count = 0;
}

void *spidpi_create(const char *name, int listen_port, int mode, int loglevel) {
  struct spidpi_ctx *ctx =
      (struct spidpi_ctx *)calloc(1, sizeof(struct spidpi_ctx));
  assert(ctx);

  ctx->loglevel = loglevel;
  ctx->mon = monitor_spi_init(mode);
  ctx->tick = 0;
  ctx->msbfirst = 1;
  ctx->nmax = 0;
  ctx->nin = 0;
  ctx->nout = 0;
  ctx->bout = 0;
  ctx->state = SP_IDLE;
  ctx->delay = 0;
  /* mode is CPOL << 1 | CPHA
   * cpol = 0 --> external clock matches internal
   * cpha = 0 --> drive on internal falling edge, capture on rising
   */
  ctx->cpol = ((mode == 0) || (mode == 2)) ? 0 : 1;
  ctx->cpha = ((mode == 1) || (mode == 3)) ? 1 : 0;
  /* CPOL = 1 for clock idle high */
  ctx->driving = P2D_CSB | ((ctx->cpol) ? P2D_SCK : 0);

  xfer_reset(ctx);

  int rv;
  char cwd[PATH_MAX];
  char *cwd_rv;
  cwd_rv = getcwd(cwd, sizeof(cwd));
  assert(cwd_rv != NULL);

  if (listen_port >= 0 && listen_port <= 0xffff) {
    // Create socket
    ctx->sock = tcp_server_create(name, listen_port);
    assert(ctx->sock);

    printf(
        "\n"
        "SPI: Created %s:%d for %s. Connect to it with any telnet terminal "
        "program.\n"
        "NOTE: a SPI transaction is run for every 4 characters entered.\n",
        "localhost", listen_port, name);
  } else {
    struct termios tty;
    cfmakeraw(&tty);

    rv = openpty(&ctx->host, &ctx->device, 0, &tty, 0);
    assert(rv != -1);

    rv = ttyname_r(ctx->device, ctx->ptyname, 64);
    assert(rv == 0 && "ttyname_r failed");

    int cur_flags = fcntl(ctx->host, F_GETFL, 0);
    assert(cur_flags != -1 && "Unable to read current flags.");
    int new_flags = fcntl(ctx->host, F_SETFL, cur_flags | O_NONBLOCK);
    assert(new_flags != -1 && "Unable to set FD flags");

    printf(
        "\n"
        "SPI: Created %s for %s. Connect to it with any terminal program, "
        "e.g.\n"
        "$ screen %s\n"
        "NOTE: a SPI transaction is run for every 4 characters entered.\n",
        ctx->ptyname, name, ctx->ptyname);
  }

  rv = snprintf(ctx->mon_pathname, PATH_MAX, "%s/%s.log", cwd, name);
  assert(rv <= PATH_MAX && rv > 0);
  ctx->mon_file = fopen(ctx->mon_pathname, "w");
  if (ctx->mon_file == NULL) {
    fprintf(stderr, "SPI: Unable to open file at %s: %s\n", ctx->mon_pathname,
            strerror(errno));
    return NULL;
  }
  // more useful for tail -f
  setlinebuf(ctx->mon_file);
  printf(
      "SPI: Monitor output file created at %s. Works well with tail:\n"
      "$ tail -f %s\n",
      ctx->mon_pathname, ctx->mon_pathname);

  return (void *)ctx;
}

char spidpi_tick(void *ctx_void, const svLogicVecVal *d2p_data) {
  struct spidpi_ctx *ctx = (struct spidpi_ctx *)ctx_void;
  assert(ctx);
  int d2p = d2p_data->aval;

  // Will tick at the host clock
  ctx->tick++;

#ifdef CONTROL_TRACE
  if (ctx->tick == 4) {
    VerilatorSimCtrl::GetInstance().TraceOff();
  }
#endif

  monitor_spi(ctx->mon, ctx->mon_file, ctx->loglevel, ctx->tick, ctx->driving,
              d2p);

  if (ctx->state == SP_IDLE) {
    bool valid;

    do {
      char buf;
      valid = false;
      if (ctx->sock) {
        if (tcp_server_read(ctx->sock, &buf)) {
          valid = true;
        }
      } else {
        int result;
        if ((result = read(ctx->host, &buf, 1)) == 1) {
          valid = true;
        } else if (result == -1) {
          if (errno != EAGAIN) {
            xfer_reset(ctx);
            fprintf(stderr, "Read on SPI FIFO gave %s\n", strerror(errno));
          }
        }
      }
      if (valid) {
        if (buf == '\n') {
          // Eat newlines
        } else if (ctx->xfer_start) {
          ctx->xfer_buf_in[ctx->xfer_count++] = buf;
          switch (buf) {
            case '{':
              ctx->xfer_indent++;
              break;
            case '}':
              ctx->xfer_indent--;
              break;
            default:
              break;
          }
          if (ctx->xfer_indent == 0) {
            ctx->xfer_finish = true;
          }
        } else if (buf == '{') {
          ctx->xfer_buf_in[ctx->xfer_count++] = buf;
          ctx->xfer_indent = 1;
          ctx->xfer_start = true;
        } else {
          xfer_reset(ctx);
          fprintf(stderr, "Invalid character in transaction stream\n");
        }
      }
    } while (valid && ctx->xfer_max > ctx->xfer_count && !ctx->xfer_finish);
    if (ctx->xfer_count >= ctx->xfer_max && !ctx->xfer_finish) {
      fprintf(stderr, "Transaction size bigger than buffer\n");
      xfer_respond(ctx, true);
      xfer_reset(ctx);
    } else if (ctx->xfer_finish) {
      if (xfer_parse(ctx)) {
        ctx->nout = 0;
        ctx->nin = 0;
        ctx->bout = ctx->msbfirst ? 0x80 : 0x01;
        ctx->bin = ctx->msbfirst ? 0x80 : 0x01;
        ctx->din = 0;
        ctx->state = SP_CSFALL;
#ifdef CONTROL_TRACE
        VerilatorSimCtrl::GetInstance().TraceOn();
#endif
      } else {
        xfer_respond(ctx, true);
        xfer_reset(ctx);
      }
    }
  }
  // SPI clock toggles every 4th tick (i.e. freq=primary_frequency/8)
  if ((ctx->tick & 3) || (ctx->state == SP_IDLE)) {
    return ctx->driving;
  }

  // Create a set delay between transactions
  if ((ctx->delay > 0)) {
    ctx->delay--;
    return ctx->driving;
  }

  // Only get here on sck edges when active
  int internal_sck = (ctx->tick & 4) ? 1 : 0;
  int set_sck = (internal_sck ? P2D_SCK : 0);
  if (ctx->cpol) {
    set_sck ^= P2D_SCK;
  }

  if (internal_sck == ctx->cpha) {
    // host driving edge (falling for mode 0)
    switch (ctx->state) {
      case SP_DMOVE:
        // SCLK low, CSB low
        ctx->driving =
            set_sck | (ctx->buf[ctx->nout] & ctx->bout) ? P2D_SDI : 0;
        ctx->bout = (ctx->msbfirst) ? ctx->bout >> 1 : ctx->bout << 1;
        if ((ctx->bout & 0xff) == 0) {
          ctx->bout = ctx->msbfirst ? 0x80 : 0x01;
          ctx->nout++;
          if (ctx->nout == ctx->nmax) {
            ctx->state = SP_LASTBIT;
          }
        }
        break;
      case SP_LASTBIT:
        ctx->state = SP_CSRISE;
        // fallthrough
      default:
        ctx->driving = set_sck | (ctx->driving & ~P2D_SCK);
        break;
    }
  } else {
    // host other edge (rising for mode 0)
    switch (ctx->state) {
        // Read input data (opposite edge to sending)
        // both DMOVE and LASTBIT states are data moving ones!
      case SP_DMOVE:
      case SP_LASTBIT:
        ctx->din = ctx->din | ((d2p & D2P_SDO) ? ctx->bin : 0);
        ctx->bin = (ctx->msbfirst) ? ctx->bin >> 1 : ctx->bin << 1;
        if (ctx->bin == 0) {
          ctx->buf[ctx->nin++] = ctx->din;
          ctx->bin = (ctx->msbfirst) ? 0x80 : 0x01;
          ctx->din = 0;
        }
        ctx->driving = set_sck | (ctx->driving & ~P2D_SCK);
        break;
      case SP_CSFALL:
        if (ctx->nmax > 0) {
          // CSB low, drive SDI to first bit
          ctx->driving =
              (set_sck | (ctx->buf[ctx->nout] & ctx->bout) ? P2D_SDI : 0);
          ctx->state = SP_DMOVE;
        } else {
          ctx->state = SP_CSRISE;
        }
        break;
      case SP_CSRISE:
        xfer_respond_next_trans(ctx);
        if ((ctx->xfer_next = xfer_parse_next_trans(ctx, ctx->xfer_next)) !=
            NULL) {
          ctx->nout = 0;
          ctx->nin = 0;
          ctx->bout = ctx->msbfirst ? 0x80 : 0x01;
          ctx->bin = ctx->msbfirst ? 0x80 : 0x01;
          ctx->din = 0;
          ctx->state = SP_CSFALL;
#ifdef CONTROL_TRACE
          VerilatorSimCtrl::GetInstance().TraceOn();
#endif
        } else {
          // CSB high, clock stopped
          ctx->driving = P2D_CSB;
          ctx->state = SP_IDLE;
          // TODO: Make this configurable.
          ctx->delay = 1000;
          xfer_respond(ctx, false);
          xfer_reset(ctx);
        }
        break;
      case SP_FINISH:
#ifdef CONTROL_TRACE
        VerilatorSimCtrl::GetInstance().RequestStop(true);
#endif
        break;
      default:
        ctx->driving = set_sck | (ctx->driving & ~P2D_SCK);
        break;
    }
  }
  return ctx->driving;
}

void spidpi_close(void *ctx_void) {
  struct spidpi_ctx *ctx = (struct spidpi_ctx *)ctx_void;
  if (!ctx) {
    return;
  }

  if (ctx->sock) {
    tcp_server_close(ctx->sock);
  } else {
    close(ctx->host);
    close(ctx->device);
  }

  if (ctx->mon_file) {
    fflush(ctx->mon_file);
    fclose(ctx->mon_file);
  }

  free(ctx);
}
