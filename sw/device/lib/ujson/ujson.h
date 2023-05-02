// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_UJSON_UJSON_H_
#define OPENTITAN_SW_DEVICE_LIB_UJSON_UJSON_H_
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#ifdef __cplusplus
extern "C" {
#endif

/**
 * Input/Output context for ujson.
 */
typedef struct ujson {
  /** A generic pointer holding context for the IO routines. */
  void *io_context;
  /** A pointer to an IO function for writing data to the output. */
  status_t (*putbuf)(void *, const char *, size_t);
  /** A pointer to an IO function for reading data from the input. */
  status_t (*getc)(void *);
  /** An internal single character buffer for ungetting a character. */
  int16_t buffer;
  /** Holds the rolling CRC32 of characters that are sent and received.*/
  uint32_t crc32;
} ujson_t;

// clang-format off
#define UJSON_INIT(context_, getc_, putbuf_) \
  {                                          \
    .io_context = (void*)(context_),         \
    .putbuf_ = (putbuf_),                    \
    .getc = (getc_),                         \
    .buffer = -1,                            \
    .crc32 = UINT32_MAX,                     \
  }
// clang-format on

/**
 * Initializes and returns a ujson context.
 *
 * @param context An IO context for the `getc` and `putbuf` functions.
 * @param getc A function to read a character from the input.
 * @param putbuf A function to write a buffer to the output.
 * @return An initialized ujson_t context.
 */
ujson_t ujson_init(void *context, status_t (*getc)(void *),
                   status_t (*putbuf)(void *, const char *, size_t));

/**
 * Gets a single character from the input.
 *
 * @param uj A ujson IO context.
 * @return The next character or an error.
 */
status_t ujson_getc(ujson_t *uj);

/**
 * Pushes a single character back to the input.
 *
 * @param uj A ujson IO context.
 * @param ch The character to put back to the input buffer.
 * @return OK or an error.
 */
status_t ujson_ungetc(ujson_t *uj, char ch);

/**
 * Writes a buffer to the output.
 *
 * @param uj A ujson IO context.
 * @param buf The buffer to write to the output.
 * @param len The length of the buffer.
 * @return OK or an error.
 */
status_t ujson_putbuf(ujson_t *uj, const char *buf, size_t len);

/**
 * Resets the CRC32 calculation to an initial state.
 *
 * @param uj A ujson IO context.
 */
void ujson_crc32_reset(ujson_t *uj);

/**
 * Returns the finished value of a CRC32 calculation.
 *
 * Note the state is un-altered by this function.
 * One must reset before starting a new calculation.
 *
 * @param uj A ujson IO context.
 * @return The final value for the CRC32 calculation.
 */
uint32_t ujson_crc32_finish(ujson_t *uj);

/**
 * Compares two strings for equality.
 *
 * @param a A string.
 * @param b A string.
 * @return true of the strings are equal; false otherwise.
 */
bool ujson_streq(const char *a, const char *b);

/**
 * Consumes a character from the input.
 *
 * Consume all whitespace until a non-whitespace character is found.
 * The non-whitespace character must be `ch`.
 *
 * @param uj A ujson IO context.
 * @param ch The character to consume.
 * @return OK or an error.
 */
status_t ujson_consume(ujson_t *uj, char ch);

/**
 * Find and consume a character from the input.
 *
 * Consume all whitespace until a non-whitespace character is found.
 * If the character is `ch`, return OK(1).
 * If the character is not `ch`, unget the character and return OK(0).
 *
 * @param uj A ujson IO context.
 * @param ch The character to consume.
 * @return OK or an error.
 */
status_t ujson_consume_maybe(ujson_t *uj, char ch);

/**
 * Parse a JSON quoted string.
 *
 * Consume whitespace until finding a double-quote.  Consume all characters
 * (obeying json escape sequences) until the next double-quote.  If the
 * input string exceeds the length of the user buffer, the user
 * buffer will contain a truncated string and the entire input json string
 * will be consumed.
 *
 * @param uj A ujson IO context.
 * @param str A buffer to write the string into.
 * @param len The length of the target buffer.
 * @return OK or an error.
 */
status_t ujson_parse_qs(ujson_t *uj, char *str, size_t len);

/**
 * Parse a JSON integer.
 *
 * @param uj A ujson IO context.
 * @param result: The parsed integer.
 * @param rsz: The size of the integer (in bytes).
 * @return OK or an error.
 */
status_t ujson_parse_integer(ujson_t *uj, void *result, size_t rsz);

/**
 * The following functions parse integers of specific sizes.
 */
status_t ujson_deserialize_uint64_t(ujson_t *uj, uint64_t *value);
status_t ujson_deserialize_uint32_t(ujson_t *uj, uint32_t *value);
status_t ujson_deserialize_uint16_t(ujson_t *uj, uint16_t *value);
status_t ujson_deserialize_uint8_t(ujson_t *uj, uint8_t *value);
status_t ujson_deserialize_size_t(ujson_t *uj, size_t *value);
status_t ujson_deserialize_int64_t(ujson_t *uj, int64_t *value);
status_t ujson_deserialize_int32_t(ujson_t *uj, int32_t *value);
status_t ujson_deserialize_int16_t(ujson_t *uj, int16_t *value);
status_t ujson_deserialize_int8_t(ujson_t *uj, int8_t *value);

/**
 * Deserialize a boolean.
 *
 * @param uj A ujson IO context.
 * @param value Pointer to the value to deserialize into.
 * @return OK or an error.
 */
status_t ujson_deserialize_bool(ujson_t *uj, bool *value);

/**
 * Deserialize a status_t.
 *
 * @param uj A ujson IO context.
 * @param value Pointer to the value to deserialize into.
 * @return OK or an error.
 */
status_t ujson_deserialize_status_t(ujson_t *uj, status_t *value);

/**
 * Serialize a string.
 *
 * @param uj A ujson IO context.
 * @param buf The string to serialize.
 * @return OK or an error.
 */
status_t ujson_serialize_string(ujson_t *uj, const char *buf);

/**
 * Serialize an integer.
 *
 * @param uj A ujson IO context.
 * @param value A pointer to the integer to serialize.
 * @return OK or an error.
 */
status_t ujson_serialize_uint64_t(ujson_t *uj, const uint64_t *value);
status_t ujson_serialize_uint32_t(ujson_t *uj, const uint32_t *value);
status_t ujson_serialize_uint16_t(ujson_t *uj, const uint16_t *value);
status_t ujson_serialize_uint8_t(ujson_t *uj, const uint8_t *value);
status_t ujson_serialize_size_t(ujson_t *uj, const size_t *value);
status_t ujson_serialize_int64_t(ujson_t *uj, const int64_t *value);
status_t ujson_serialize_int32_t(ujson_t *uj, const int32_t *value);
status_t ujson_serialize_int16_t(ujson_t *uj, const int16_t *value);
status_t ujson_serialize_int8_t(ujson_t *uj, const int8_t *value);

/**
 * Serialize a boolean.
 *
 * @param uj A ujson IO context.
 * @param value Pointer to the value to serialize.
 * @return OK or an error.
 */
status_t ujson_serialize_bool(ujson_t *uj, const bool *value);

/**
 * Serialize a status_t.
 *
 * @param uj A ujson IO context.
 * @param value Pointer to the value to serialize.
 * @return OK or an error.
 */
status_t ujson_serialize_status_t(ujson_t *uj, const status_t *value);

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_UJSON_UJSON_H_
