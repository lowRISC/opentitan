// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _MSG_PRINT_H_
#define _MSG_PRINT_H_

#include "uart.h"

#define _xstr(a) _str(a)
#define _str(a) #a
#define VA_ARGS(...) , ##__VA_ARGS__

// The following set of macros are used by the standard msg print macro
// flavors in ../msg.h

/** print the final msg consisting of header and the msg string
 *
 * calls msg_print() function to process formatted string and insert args
 * uses UART to pring msg string character by character
 * Do not invoke this macro directly; use  the standard
 */
#define MSG_PRINT(msg_header, fmt, ...) \
  msg_print(uart_send_char, msg_header, fmt VA_ARGS(__VA_ARGS__));

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

/** msg type amd verbosity strings
 */
#define MSG_TYPE_INFO "INFO"
#define MSG_TYPE_WARNING "WARNING"
#define MSG_TYPE_ERROR "ERROR"
#define MSG_TYPE_FATAL "FATAL"
#define MSG_VERB_NONE ""
#define MSG_VERB_LOW "[LO]"
#define MSG_VERB_MEDIUM "[MED]"
#define MSG_VERB_HIGH "[HI]"
#define MSG_VERB_FULL "[FULL]"
#define MSG_VERB_DEBUG "[DBG]"

#endif  // _MSG_PRINT_H_
