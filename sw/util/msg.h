// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _MSG_H_
#define _MSG_H_

#include "msg_impl.h"

/**
 * The APIs below for printing msgs in SW take a formatted string with variable
 * number of arguments. The APIs are designed to provide a way for attaching the
 * msg type, verbosity, file name and the line number information along with the
 * msg to provide an easier path to debug. These parameters form the msg header
 * which is prepended to the actual msg being printed. The following provides a
 * brief description for these:
 *
 *  msg_type:     severity of the msg: info, warning, error or fatal This is
 *                indicated using MSG_TYPE_* set of macros which are set to
 *                empty strings by default.
 *
 *  verbosity:    (applicable only to info msgs) none, low, medium, high, full
 *                and debug. Based on desired verbosity, visibility of certain
 *                msgs can be turned off. This is expected to be done externally
 *                (for example, if the print msgs go to a log, the desired
 *                verbosity msgs can be greped and filtered out). This is
 *                indicated using the MSG_VERB_* set of macros which are set to
 *                empty strings by default.
 *
 *  file name:    name of the file using __FILE__
 *
 *  line number:  line where the print originated using __LINE__
 *
 * Printing the final msg
 * Once the header is constructed, another API is invoked that takes header
 * and the formatted msg as arg and prints the whole msg using the desired
 * implementation. This is provided by the MSG_PRINT() macro.
 *
 * All of these macros defined in this file can be overridden to customize the
 * flow based on the desired requirement. This is done in the msg_impl.h header
 * file, placed in sw/util/msg_<impl> directory. The correct msg_impl.h is
 * selected by the build system which resolves the dependency based on the
 * target.
 */

/** Generic msg print APIs
 *
 * The following are a set of msg print APIs available for use in OpenTitan SW.
 * These are implemented as macros so that based on need, it could expand to a
 * function call or another macro invocation.
 *
 * @param fmt: formatted string msg that take variable # of args
 * @param ...: # of args passed to fmt
 */
// print an info msg with no verbosity
#ifndef MSG_INFO
#warning MSG_INFO undefined: it will result in vacuous invocation
#define MSG_INFO(fmt, ...)
#endif

// print an info msg with low verbosity
#ifndef MSG_INFO_LOW
#warning MSG_INFO_LOW undefined: it will result in vacuous invocation
#define MSG_INFO_LOW(fmt, ...)
#endif

// print an info msg with medium verbosity
#ifndef MSG_INFO_MEDIUM
#warning MSG_INFO_MEDIUM undefined: it will result in vacuous invocation
#define MSG_INFO_MEDIUM(fmt, ...)
#endif

// print an info msg with high verbosity
#ifndef MSG_INFO_HIGH
#warning MSG_INFO_HIGH undefined: it will result in vacuous invocation
#define MSG_INFO_HIGH(fmt, ...)
#endif

// print an info msg with full verbosity
#ifndef MSG_INFO_FULL
#warning MSG_INFO_FULL undefined: it will result in vacuous invocation
#define MSG_INFO_FULL(fmt, ...)
#endif

// print an info msg with debug verbosity
#ifndef MSG_INFO_DEBUG
#warning MSG_INFO_DEBUG undefined: it will result in vacuous invocation
#define MSG_INFO_DEBUG(fmt, ...)
#endif

// print a warning msg
#ifndef MSG_WARNING
#warning MSG_WARNING undefined: it will result in vacuous invocation
#define MSG_WARNING(fmt, ...)
#endif

// print an error msg
#ifndef MSG_ERROR
#warning MSG_ERROR undefined: it will result in vacuous invocation
#define MSG_ERROR(fmt, ...)
#endif

// print a fatal error msg
#ifndef MSG_FATAL
#warning MSG_FATAL undefined: it will result in vacuous invocation
#define MSG_FATAL(fmt, ...)
#endif

/** Msg type and verbosity string constants (used to construct msg header)
 *
 * These are strings used to construct the msg header.
 */

#ifndef MSG_TYPE_INFO
#define MSG_TYPE_INFO ""
#endif

#ifndef MSG_TYPE_WARNING
#define MSG_TYPE_WARNING ""
#endif

#ifndef MSG_TYPE_ERROR
#define MSG_TYPE_ERROR ""
#endif

#ifndef MSG_TYPE_FATAL
#define MSG_TYPE_FATAL ""
#endif

#ifndef MSG_VERB_NONE
#define MSG_VERB_NONE ""
#endif

#ifndef MSG_VERB_LOW
#define MSG_VERB_LOW ""
#endif

#ifndef MSG_VERB_MEDIUM
#define MSG_VERB_MEDIUM ""
#endif

#ifndef MSG_VERB_HIGH
#define MSG_VERB_HIGH ""
#endif

#ifndef MSG_VERB_FULL
#define MSG_VERB_FULL ""
#endif

#ifndef MSG_VERB_DEBUG
#define MSG_VERB_DEBUG ""
#endif

/** Msg header macro
 *
 * This macro provides a way to construct the header string using the above
 * string constants. This is implementation specific.
 */
#ifndef MSG_HEADER
#define MSG_HEADER(msg_type, verbosity)
#endif

/** Msg print macro
 *
 * The generic msg print APIs above are expected to call this underneath and
 * provide a way to suppliment the msg being printed with a header. This is
 * implementation specific.
 */
#ifndef MSG_PRINT
#warning MSG_PRINT undefined: it will result in vacuous invocation
#define MSG_PRINT(msg_header, fmt, ...)
#endif

#endif  // _MSG_H_
