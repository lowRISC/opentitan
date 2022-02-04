// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/host/spiflash/verilator_spi_interface.h"

#include <cstring>
#include <fcntl.h>
#include <iostream>
#include <string>
#include <termios.h>
#include <unistd.h>

#include "cryptoc/sha256.h"

namespace opentitan {
namespace spiflash {
namespace {

/** Configure `fd` as a serial port with baud rate 9600. */
bool SetTermOpts(int fd) {
  struct termios options;
  if (tcgetattr(fd, &options) != 0) {
    return false;
  }
  cfmakeraw(&options);
  // The current Verilator configuration uses 9600 baud rate.
  if (cfsetispeed(&options, B9600) != 0) {
    return false;
  }
  if (cfsetospeed(&options, B9600) != 0) {
    return false;
  }
  if (tcsetattr(fd, TCSANOW, &options) != 0) {
    return false;
  }
  return true;
}

/**
 * Returns file handle on success, or -1 on failure. This function
 * configures de file handle to behave as a serial port with baud rate 9600,
 * which is the baud rate supported by Verilator.
 */
int OpenDevice(const std::string &filename) {
  int fd =
      open(filename.c_str(), O_RDWR | O_NOCTTY | /* O_NONBLOCK | */ O_CLOEXEC);
  if (fd < 0) {
    std::cerr << "Failed to open device: " << filename << std::endl;
    return fd;
  }
  if (!SetTermOpts(fd)) {
    close(fd);
    return -1;
  }
  return fd;
}

}  // namespace

VerilatorSpiInterface::~VerilatorSpiInterface() {
  if (fd_ != -1) {
    close(fd_);
  }
}

bool VerilatorSpiInterface::Init() {
  fd_ = OpenDevice(options_.target);
  if (fd_ < 0) {
    return false;
  }
  return true;
}

bool VerilatorSpiInterface::TransmitFrame(const uint8_t *tx, size_t size) {
  size_t bytes_written = 0;
  size_t bytes_read = 0;

  rx_.resize(size);

  while (bytes_written != size || bytes_read != size) {
    if (bytes_written != size) {
      ssize_t write_size = size - bytes_written >= 4 ? 4 : size - bytes_written;
      write_size = write(fd_, &tx[bytes_written], write_size);
      switch (write_size) {
        case -1:
          if (errno != EAGAIN && errno != EWOULDBLOCK) {
            std::cerr << "Failed to write bytes to spi interface, errno: "
                      << strerror(errno) << ". Bytes written: " << bytes_written
                      << " expected: " << size << std::endl;
            return false;
          }
          break;
        default:
          bytes_written += write_size;
          break;
      }
    }

    if (bytes_read != size) {
      ssize_t read_size = size - bytes_read >= 4 ? 4 : size - bytes_read;
      read_size = read(fd_, &rx_[bytes_read], read_size);
      switch (read_size) {
        case -1:
          if (errno != EAGAIN && errno != EWOULDBLOCK) {
            std::cerr << "Failed to read bytes from spi interface, errno: "
                      << strerror(errno) << ". Bytes read: " << bytes_read
                      << " expected: " << size << std::endl;
            return false;
          }
          break;
        default:
          bytes_read += read_size;
          break;
      }
    }
  }
  usleep(options_.frame_process_delay_us);
  return true;
}

bool VerilatorSpiInterface::CheckHash(const uint8_t *tx, size_t size) {
  uint8_t hash[SHA256_DIGEST_SIZE];
  SHA256_hash(tx, size, hash);

  for (int i = 0; i < SHA256_DIGEST_SIZE; i++) {
    if (rx_[i] != hash[SHA256_DIGEST_SIZE - i - 1]) {
      return false;
    }
  }

  return true;
}
}  // namespace spiflash
}  // namespace opentitan
