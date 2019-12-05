// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/aes.h"
#include "sw/device/lib/common.h"
#include "sw/device/lib/hw_sha256.h"
#include "sw/device/lib/uart.h"

#define LENGTH_KEY 32
#define MAX_LENGTH_TEXT 128

/**
 * Wait for user to confirm current content of input string buffer or overwrite
 * this buffer with new input over UART. The function stops processing input
 * once a carriage return is received or when the input string buffer is full.
 *
 * @param input_string pointer to string buffer.
 * @param length_max   size of the string buffer.
 */
void overwrite_string(char *input_string, size_t length_max) {
  bool done = false;
  int ret = -1;
  char my_char = 0;
  int index = 0;

  while (done == false) {
    ret = uart_rcv_char(&my_char);

    if (ret == 0) {
      if (my_char == 13) {
        // A carriage return ends the input processing.
        if (index > 0) {
          // We have overwritten the input string, zero remaining characters.
          for (int i = index; i < length_max; ++i) {
            input_string[i] = '\0';
          }
        }
        uart_send_str("\r\n");
        done = true;
      } else {
        // Other characters are echoed and forwarded to the string buffer.
        uart_send_str(&my_char);
        input_string[index++] = my_char;
        if (index == length_max) {
          uart_send_str("\r\n");
          done = true;
        }
      }
    }
  }
}

/**
 * Let the AES unit process multiple blocks.
 *
 * @param data_out   pointer to output buffer.
 * @param data_in    pointer to input buffer.
 * @param num_blocks number of 16-byte blocks to process.
 */
void aes_process_blocks(void *data_out, const void *data_in, int num_blocks) {
  uint32_t *word_ptr_out = (uint32_t *)data_out;
  const uint32_t *word_ptr_in = (uint32_t *)data_in;

  if (num_blocks > 0) {
    // Write Input Data Block 0
    aes_data_put_wait((const void *)word_ptr_in);

    if (num_blocks > 1) {
      // Write Input Data Block 1
      aes_data_put_wait((const void *)&word_ptr_in[4]);
    }

    // For Data Block I=0,...,N-1
    for (int i = 0; i < num_blocks; ++i) {
      // Read Output Data Block I
      aes_data_get_wait(&word_ptr_out[i * 4]);

      // Write Input Data Block I+2 - For I=0,...,N-3 only.
      if (i < num_blocks - 2) {
        aes_data_put((const void *)&word_ptr_in[4 * (i + 2)]);
      }
    }
  }
}

/**
 * Prints |data_in| in hex byte format. 16 bytes per row.
 */
void print_hex_buffer(char *data_in, size_t length) {
  for (int i = 0; i < length; ++i) {
    uart_send_str("0x");
    uart_send_uint((uint32_t)data_in[i], 8);
    uart_send_str(" ");
    if (!((i + 1) % 16)) {
      uart_send_str("\r\n");
    }
  }
}

/**
 * Returns non-zero if |initial| != |final|
 */
int check_hash(char initial[32], char final[32]) {
  uint8_t result = 0;
  for (int i = 0; i < 32; ++i) {
    result |= initial[i] ^ final[i];
  }
  return result;
}

int main(int argc, char **argv) {
  uart_init(UART_BAUD_RATE);
  uart_send_str("Running AES HMAC demo\r\n");

  // Global variables
  char plain_text[MAX_LENGTH_TEXT] = "Welcome to the RISC-V Summit 2019!";
  char cipher_text[MAX_LENGTH_TEXT];
  char aes_key[LENGTH_KEY] = "This key is not really secret.";
  int num_blocks = MAX_LENGTH_TEXT / 16;
  char digest_initial[32];
  char digest_final[32];

  aes_cfg_t aes_cfg;
  aes_cfg.key_len = kAes256;
  aes_cfg.manual_start_trigger = false;
  aes_cfg.force_data_overwrite = false;

  // Get Input
  uart_send_str("I will encode and hash the following plain text: \r\n\"");
  uart_send_str(plain_text);
  uart_send_str("\"\r\n");
  uart_send_str(
      "Please enter your own plain text to change it. Otherwise hit "
      "ENTER.\r\n");
  overwrite_string(plain_text, MAX_LENGTH_TEXT);
  uart_send_str("\r\n");

  uart_send_str("I will use the following AES-256 key: \r\n\"");
  uart_send_str(aes_key);
  uart_send_str("\"\r\n");
  uart_send_str(
      "Please enter your own key to change it. Otherwise hit ENTER.\r\n");
  overwrite_string(aes_key, LENGTH_KEY);
  uart_send_str("\r\n");

  // Determine number of 16-byte blocks to encode
  for (int i = 0; i < MAX_LENGTH_TEXT; ++i) {
    if (plain_text[i] == '\0') {
      num_blocks = i / 16;
      if (num_blocks * 16 < i) {
        ++num_blocks;
      }
      break;
    }
  }

  // Calculate hash over plain text before encryption.
  hw_SHA256_hash(plain_text, ARRAYSIZE(plain_text), (uint8_t *)digest_initial);

  uart_send_str("Plain text hash: \r\n");
  print_hex_buffer(digest_initial, ARRAYSIZE(digest_initial));

  // Configure AES key
  aes_key_put((const void *)aes_key, aes_cfg.key_len);

  // Encode
  aes_cfg.mode = kAesEnc;
  aes_init(aes_cfg);
  aes_process_blocks((void *)cipher_text, (const void *)plain_text, num_blocks);

  // Output
  uart_send_str("Encrypted cipher text: \r\n");
  print_hex_buffer(cipher_text, num_blocks * 16);
  uart_send_str("\n");

  // Decode
  aes_cfg.mode = kAesDec;
  aes_init(aes_cfg);
  aes_process_blocks((void *)plain_text, (const void *)cipher_text, num_blocks);

  // Output
  uart_send_str("Decrypted cipher text: \r\n\"");
  uart_send_str(plain_text);
  uart_send_str("\"\r\n\n");

  // Calculate hash over recovered plain text after decryption.
  hw_SHA256_hash(plain_text, ARRAYSIZE(plain_text), (uint8_t *)digest_final);
  if (check_hash(digest_initial, digest_final)) {
    uart_send_str("Detected hash mismatch on decrypted data!. Got: \r\n");
    print_hex_buffer(digest_final, ARRAYSIZE(digest_final));
    uart_send_str("Expected: \r\n");
    print_hex_buffer(digest_initial, ARRAYSIZE(digest_initial));
  }

  uart_send_str("DONE!\r\n");
  __asm__ volatile("wfi;");

  return 0;
}
