// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_FLOAT_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_FLOAT_H_

/**
 * @file
 * @brief C library Floating-point environment (Freestanding)
 *
 * This header implements the float.h standard header, as required by C11 S4p6.
 * This header is specified in detail in S7.7 and S5.2.4.2.2 of the same.
 *
 * The compiler-defined names below are cribbed from
 * https://clang.llvm.org/doxygen/float_8h_source.html
 */

#define FLT_EVAL_METHOD __FLT_EVAL_METHOD__ /**< @hideinitializer */
#define FLT_ROUNDS (-1)                     /**< @hideinitializer */
#define FLT_RADIX __FLT_RADIX__             /**< @hideinitializer */

#define FLT_MANT_DIG __FLT_MANT_DIG__   /**< @hideinitializer */
#define DBL_MANT_DIG __DBL_MANT_DIG__   /**< @hideinitializer */
#define LDBL_MANT_DIG __LDBL_MANT_DIG__ /**< @hideinitializer */

#define DECIMAL_DIG __DECIMAL_DIG__ /**< @hideinitializer */

#define FLT_DIG __FLT_DIG__   /**< @hideinitializer */
#define DBL_DIG __DBL_DIG__   /**< @hideinitializer */
#define LDBL_DIG __LDBL_DIG__ /**< @hideinitializer */

#define FLT_MIN_EXP __FLT_MIN_EXP__   /**< @hideinitializer */
#define DBL_MIN_EXP __DBL_MIN_EXP__   /**< @hideinitializer */
#define LDBL_MIN_EXP __LDBL_MIN_EXP__ /**< @hideinitializer */

#define FLT_MIN_10_EXP __FLT_MIN_10_EXP__   /**< @hideinitializer */
#define DBL_MIN_10_EXP __DBL_MIN_10_EXP__   /**< @hideinitializer */
#define LDBL_MIN_10_EXP __LDBL_MIN_10_EXP__ /**< @hideinitializer */

#define FLT_MAX_EXP __FLT_MAX_EXP__   /**< @hideinitializer */
#define DBL_MAX_EXP __DBL_MAX_EXP__   /**< @hideinitializer */
#define LDBL_MAX_EXP __LDBL_MAX_EXP__ /**< @hideinitializer */

#define FLT_MAX_10_EXP __FLT_MAX_10_EXP__   /**< @hideinitializer */
#define DBL_MAX_10_EXP __DBL_MAX_10_EXP__   /**< @hideinitializer */
#define LDBL_MAX_10_EXP __LDBL_MAX_10_EXP__ /**< @hideinitializer */

#define FLT_MAX __FLT_MAX__   /**< @hideinitializer */
#define DBL_MAX __DBL_MAX__   /**< @hideinitializer */
#define LDBL_MAX __LDBL_MAX__ /**< @hideinitializer */

#define FLT_EPSILON __FLT_EPSILON__   /**< @hideinitializer */
#define DBL_EPSILON __DBL_EPSILON__   /**< @hideinitializer */
#define LDBL_EPSILON __LDBL_EPSILON__ /**< @hideinitializer */

#define FLT_MIN __FLT_MIN__   /**< @hideinitializer */
#define DBL_MIN __DBL_MIN__   /**< @hideinitializer */
#define LDBL_MIN __LDBL_MIN__ /**< @hideinitializer */

#define FLT_TRUE_MIN __FLT_DENORM_MIN__   /**< @hideinitializer */
#define DBL_TRUE_MIN __DBL_DENORM_MIN__   /**< @hideinitializer */
#define LDBL_TRUE_MIN __LDBL_DENORM_MIN__ /**< @hideinitializer */

#define FLT_DECIMAL_DIG __FLT_DECIMAL_DIG__   /**< @hideinitializer */
#define DBL_DECIMAL_DIG __DBL_DECIMAL_DIG__   /**< @hideinitializer */
#define LDBL_DECIMAL_DIG __LDBL_DECIMAL_DIG__ /**< @hideinitializer */

#define FLT_HAS_SUBNORM __FLT_HAS_DENORM__   /**< @hideinitializer */
#define DBL_HAS_SUBNORM __DBL_HAS_DENORM__   /**< @hideinitializer */
#define LDBL_HAS_SUBNORM __LDBL_HAS_DENORM__ /**< @hideinitializer */

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_FREESTANDING_FLOAT_H_
