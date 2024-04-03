// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "usbdev_utils.h"

#include <cerrno>
#include <cstdio>
#include <cstring>
#include <ctime>
#include <fcntl.h>
#include <iostream>
#include <sys/time.h>
#include <termios.h>
#include <unistd.h>

#include "stream_test.h"

// Utility function to report an error returned from file/terminal-related
// functions.
static void report_error(const char *rsn) {
  std::cerr << "ERROR: " << rsn << ": " << strerror(errno) << " (error "
            << errno << ")" << std::endl;
}

// Open and configure a serial port connection to/from the USB device.
int port_open(const char *dev_name, bool write) {
  const char *port_type = write ? "output" : "input";
  int fd = open(dev_name, write ? O_WRONLY : O_RDONLY);
  if (fd < 0) {
    std::cerr << "ERROR: Could not open " << port_type << " port '" << dev_name
              << "'" << std::endl;
    ReportSyntax();
    return -1;
  }

  // We need to ensure that we can send full 8-bit binary data with no character
  // translations and no character echo etc.
  struct termios tty;
  if (tcgetattr(fd, &tty) != 0) {
    report_error("Failed getting terminal attributes");
    close(fd);
    return -1;
  }

  // 8 bits, no parity, no hardware handshaking.
  tty.c_cflag &= ~(PARENB | CSTOPB | CSIZE | CRTSCTS);
  tty.c_cflag |= CS8 | CREAD | CLOCAL;

  // No character echo.
  tty.c_lflag &= ~(ICANON | ECHO | ECHOE | ECHONL | ISIG);

  // No software handshaking, no special characters.
  tty.c_iflag &= ~(IXON | IXOFF | IXANY);
  tty.c_iflag &= ~(IGNBRK | BRKINT | PARMRK | ISTRIP | INLCR | IGNCR | ICRNL);

  // Disable line feed conversions and special characters on output traffic.
  tty.c_oflag &= ~(OPOST | ONLCR);

  // Non-blocking.
  tty.c_cc[VTIME] = 0;
  tty.c_cc[VMIN] = 0;

  // Set in/out baud rate to be as high as possible; just in case, but it has
  // no impact upon the measured transfer speed.
  cfsetispeed(&tty, B4000000);
  cfsetospeed(&tty, B4000000);

  // Save tty settings, also checking for error.
  if (tcsetattr(fd, TCSANOW, &tty) != 0) {
    report_error("Failed setting terminal attributes");
    close(fd);
    return -1;
  }

  return fd;
}

// Receive a sequence of bytes from the USB device, non-blocking.
ssize_t recv_bytes(int in, uint8_t *buf, size_t len) {
  ssize_t nread = 0;

  // Read as many bytes as we can from the input port.
  ssize_t n = read(in, buf, len);
  if (cfg.verbose) {
    printf("Received %zd byte(s)\n", n);
    for (int idx = 0; idx < n; idx++) {
      printf("0x%02x\n", buf[idx]);
    }
    fflush(stdout);
  }
  if (n < 0) {
    report_error("Failed to read from input port");
    return -1;
  }

  nread += n;
  buf += n;
  len -= (size_t)n;

  return nread;
}

// Send a sequence of bytes to the USB device, non-blocking.
ssize_t send_bytes(int out, const uint8_t *data, size_t len) {
  ssize_t nwritten = 0;

  if (len > 0u) {
    ssize_t n = write(out, data, len);
    if (n < 0) {
      report_error("Failed to write to output port");
      return -1;
    }

    nwritten += n;
    data += n;
    len -= n;
  }

  return nwritten;
}

// Current monotonic wall clock time in microseconds.
uint64_t time_us(void) {
  struct timeval ts;
  int ret = gettimeofday(&ts, NULL);
  if (ret < 0)
    return (uint64_t)0u;
  return ((uint64_t)ts.tv_sec * 1000000u) + ts.tv_usec;
}

// Dump a sequence of bytes as hexadecimal and ASCII for diagnostic purposes.
void buffer_dump(FILE *out, const uint8_t *data, size_t n) {
  static const char hex_digits[] = "0123456789abcdef";
  const unsigned ncols = 0x20u;
  char buf[ncols * 4u + 2u];

  while (n > 0u) {
    const unsigned chunk = (n > ncols) ? ncols : (unsigned)n;
    const uint8_t *row = data;
    unsigned idx = 0u;
    char *dp = buf;

    // Columns of hexadecimal bytes.
    while (idx < chunk) {
      dp[0] = hex_digits[row[idx] >> 4];
      dp[1] = hex_digits[row[idx++] & 0xfu];
      dp[2] = ' ';
      dp += 3;
    }
    while (idx++ < ncols) {
      dp[2] = dp[1] = dp[0] = ' ';
      dp += 3;
    }

    // Printable ASCII characters.
    for (idx = 0u; idx < chunk; idx++) {
      uint8_t ch = row[idx];
      *dp++ = (ch < ' ' || ch >= 0x80u) ? '.' : ch;
    }
    *dp = '\0';
    fprintf(out, "%s\n", buf);
    data += chunk;
    n -= chunk;
  }

  fflush(stdout);
}

// Link locations for inline functions.
extern uint64_t elapsed_time(uint64_t start);
extern uint16_t get_le16(const uint8_t *p);
