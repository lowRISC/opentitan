// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _MSG_IMPL_H
#define _MSG_IMPL_H

#include "msg_print.h"
#include "uart.h"

#define _xstr(a) _str(a)
#define _str(a) #a
#define VA_ARGS(...) , ##__VA_ARGS__

/** msg types
 *
 */
#define MSG_TYPE_INFO "INFO"
#define MSG_TYPE_WARNING "WARNING"
#define MSG_TYPE_ERROR "ERROR"
#define MSG_TYPE_FATAL "FATAL"

/** set msg_header string with type, verbosity, file and line
 *
 * This macro sets the msg_header to
 * TYPE[VERBOSITY] (file:line):
 * or
 * TYPE[VERBOSITY]: if MSG_HEADER_INCL_FILE_LINE flag is not set
 */
#ifdef MSG_HEADER_INCL_FILE_LINE
#define MSG_HEADER(msg_type, verbosity) \
  msg_type verbosity " (" __FILE__ ":" _xstr(__LINE__) "): "
#else
#define MSG_HEADER(msg_type, verbosity) msg_type verbosity ": "
#endif

/** print msgs via UART
 *
 * calls msg_print() function to process formatted string and insert args
 * uses UART to pring msg string character by character
 * Do not invoke this macro directly; use  the standard
 */
#define MSG_PRINT(msg_header, fmt, ...) \
  msg_print(uart_send_char, msg_header fmt VA_ARGS(__VA_ARGS__));

#define MSG_INFO(fmt, ...) \
  MSG_PRINT(MSG_HEADER(MSG_TYPE_INFO, MSG_VERB_NONE), fmt, __VA_ARGS__)

#define MSG_INFO_LOW(fmt, ...) \
  MSG_PRINT(MSG_HEADER(MSG_TYPE_INFO, MSG_VERB_LOW), fmt, __VA_ARGS__)

#define MSG_INFO_MEDIUM(fmt, ...) \
  MSG_PRINT(MSG_HEADER(MSG_TYPE_INFO, MSG_VERB_MEDIUM), fmt, __VA_ARGS__)

#define MSG_INFO_HIGH(fmt, ...) \
  MSG_PRINT(MSG_HEADER(MSG_TYPE_INFO, MSG_VERB_HIGH), fmt, __VA_ARGS__)

#define MSG_INFO_FULL(fmt, ...) \
  MSG_PRINT(MSG_HEADER(MSG_TYPE_INFO, MSG_VERB_FULL), fmt, __VA_ARGS__)

#define MSG_INFO_DEBUG(fmt, ...) \
  MSG_PRINT(MSG_HEADER(MSG_TYPE_INFO, MSG_VERB_DEBUG), fmt, __VA_ARGS__)

#define MSG_WARNING(fmt, ...) \
  MSG_PRINT(MSG_HEADER(MSG_TYPE_WARNING, ""), fmt, __VA_ARGS__)

#define MSG_ERROR(fmt, ...) \
  MSG_PRINT(MSG_HEADER(MSG_TYPE_ERROR, ""), fmt, __VA_ARGS__)

#define MSG_FATAL(fmt, ...) \
  MSG_PRINT(MSG_HEADER(MSG_TYPE_FATAL, ""), fmt, __VA_ARGS__)

#endif  // _MSG_IMPL_H
