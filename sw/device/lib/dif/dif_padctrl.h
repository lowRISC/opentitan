// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PADCTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PADCTRL_H_

#include <stdbool.h>

// Generated.
#include "padctrl_regs.h"

#include "sw/device/lib/base/mmio.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Pad attributes.
 *
 * Some attributes have defined meanings, others are implementation defined. Not
 * all pads will support all attributes. The padctrl DIF does not check for
 * unsupported attributes. To check to see if an attribute is supported after
 * enabling it (via `dif_padctrl_attr_enable` or `dif_padctrl_attr_write`) read
 * back the attribute field (via `dif_padctrl_attr_get`). If the attribute isn't
 * supported the attribute will still be disabled (relevant bit unset in the
 * attribute field).
 */
typedef enum dif_padctrl_attr {
  kDifPadctrlAttrNone = 0,
  kDifPadctrlAttrIOInvert = 1 << 0,
  kDifPadctrlAttrOpenDrain = 1 << 2,
  kDifPadctrlAttrPullDown = 1 << 3,
  kDifPadctrlAttrPullUp = 1 << 4,
  kDifPadctrlAttrKeeper = 1 << 5,
  kDifPadctrlAttrWeakDrive = 1 << 6,
} dif_padctrl_attr_t;

/**
 * Generic padctrl DIF return codes
 */
typedef enum dif_padctrl_result {
  /**
   * Operation succeeded.
   */
  kDifPadctrlOk = 0,
  /**
   * Operation failed due to an unspecified error. It cannot be recovered or
   * retried. */
  kDifPadctrlError = 1,
  /**
   * Operation failed due to a bad argument and can be retried. No register
   * reads or writes have been performed.
   */
  kDifPadctrlBadArg = 2,
} dif_padctrl_result_t;

/**
 * Pad kinds.
 *
 * A pad can be an MIO or DIO pad
 */
typedef enum dif_padctrl_pad_kind {
  /**
   * MIO (Multiplexed Input/Output) pad. Connected via pinmux.
   */
  kDifPadctrlPadMio = 0,
  /**
   * DIO (Dedicated Input/Output) pad. Connected directly to peripheral inputs
   * and outputs, bypassing pinmux.
   */
  kDifPadctrlPadDio,
} dif_padctrl_pad_kind_t;

/**
 * Pad index.
 *
 * Combined with `dif_padctrl_pad_kind_t` to refer to a specific pad.
 */
typedef uint32_t dif_padctrl_pad_index_t;

/**
 * Padctrl instance state.
 *
 * Padctrl persistent data that is required by the Padctrl API.
 */
typedef struct dif_padctrl {
  mmio_region_t base_addr; /**< Padctrl base address. */
} dif_padctrl_t;

/**
 * Initialises an instance of Padctrl.
 *
 * Information that must be retained, and is required to program Padctrl, shall
 * be stored in @p padctrl.
 *
 * @param base_addr Base address of an isntance of the Padctrl IP block
 * @param padctrl Padctrl state data
 * @return dif_padctrl_init_result_t.
 */
dif_padctrl_result_t dif_padctrl_init(mmio_region_t base_addr,
                                      dif_padctrl_t *padctrl);

/**
 * Padctrl reset routine error codes.
 */
typedef enum dif_padctrl_reset_result {
  kDifPadctrlResetOk = kDifPadctrlOk,
  kDifPadctrlResetError = kDifPadctrlError,
  kDifPadctrlResetBadArg = kDifPadctrlBadArg,
  /**
   * Peripheral is locked and cannot be reset. Only a read has been performed
   * and this error is recoverable but any operation that writes to the
   * registers will fail.
   */
  kDifPadctrlResetLocked,
} dif_padctrl_reset_result_t;

/**
 * Resets padctrl by writing a given set of attributes to every pad
 *
 * @param padctrl Padctrl state data
 * @param reset_attrs Attributes to write to every pad
 * @return dif_padctrl_result_t
 */
dif_padctrl_reset_result_t dif_padctrl_reset(dif_padctrl_t *padctrl,
                                             dif_padctrl_attr_t reset_attrs);

/**
 * Locks the padctrl registers.
 *
 * After the registers have been locked, they can only be unlocked by the
 * system reset.
 *
 * @param padctrl Padctrl state data.
 * @return dif_padctrl_result_t.
 */
dif_padctrl_result_t dif_padctrl_lock(dif_padctrl_t *padctrl);

/**
 * Padctrl attribute change routines error codes.
 */
typedef enum dif_padctrl_change_attr_result {
  kDifPadctrlChangeAttrOk = kDifPadctrlOk,
  kDifPadctrlChangeAttrError = kDifPadctrlError,
  kDifPadctrlChangeAttrBadArg = kDifPadctrlBadArg,
  /**
   * Peripheral is locked and attributes cannot be changed. Only a read has been
   * performed and this error is recoverable but any operation that writes to
   * the registers will fail.
   */
  kDifPadctrlChangeAttrLocked,
  /**
   * Attribute change failed because it would result in conflicting attributes
   * conflicts with another already enabled attribute. No write to the attribute
   * registers has been attemped. The change can be re-attempted with different
   * bits. This could also occur if the attribute register already contained a
   * conflicting set of attributes (e.g. because they have been written outside
   * of the DIF with conflicting values).
   */
  kDifPadctrlChangeAttrConflict,
} dif_padctrl_change_attr_result_t;

/**
 * Enables attributes for a pad.
 *
 * Not all pads implement all attributes and some combinations of attributes
 * cannot be enabled together. `dif_padctrl_enable_attrs` will check for
 * conflicting attribute and return an appropriate error. If an attribute is not
 * supported a read of the attributes will show that is disabled. It is the
 * caller's responsibility to check an attribute is supported by reading back
 * the field with `dif_padctrl_read_attr` after enabling the attribute if an
 * attribute supported check is desired.
 *
 * Note that for additional attributes as the meaning is implementation defined
 * `dif_padctrl_enable_attrs` cannot check for invalid combinations that involve
 * them.
 *
 * @param padctrl Padctrl state data.
 * @param pad_kind Which kind of pad to enable attributes for.
 * @param pad_index Which pad to enable attributes for.
 * @param enable_attrs Attributes to enable. A set bit enables the attribute, a
 * clear bit leaves attribute in its existing state.
 * @return dif_padctrl_change_attr_result_t
 */
dif_padctrl_change_attr_result_t dif_padctrl_enable_attrs(
    const dif_padctrl_t *padctrl, dif_padctrl_pad_kind_t kind,
    dif_padctrl_pad_index_t index, dif_padctrl_attr_t enable_attrs);

/**
 * Disables attributes for a pad.
 *
 * @param padctrl Padctrl state data.
 * @param pad_kind Which kind of pad to disable attributes for.
 * @param pad_index Which pad to disable attributes for.
 * @param disable_attrs Attributes to disable. A set bit disables the attribute,
 * a clear bit leaves attribute in its existing state.
 * @return dif_padctrl_change_attr_result_t
 */
dif_padctrl_change_attr_result_t dif_padctrl_disable_attrs(
    const dif_padctrl_t *padctrl, dif_padctrl_pad_kind_t kind,
    dif_padctrl_pad_index_t index, dif_padctrl_attr_t disable_attrs);

/**
 * Write attributes for a pad.
 *
 * Not all pads implement all attributes and some combinations of attributes
 * cannot be enabled together. `dif_padctrl_enable_attr` will check for
 * conflicting attribute and return an appropriate error. If an attribute is not
 * supported a read of the attributes will show that is disabled. It is the
 * caller's responsibility to check an attribute is supported by reading back
 * the field with `dif_padctrl_read_attr` after enabling the attribute if an
 * attribute supported check is desired.
 *
 * Note that for additional attributes as the meaning is implementation defined
 * `dif_padctrl_enable_attr` cannot check for invalid combinations that involve
 * them.
 *
 * @param padctrl Padctrl state data.
 * @param pad_kind Which kind of pad to set attributes for.
 * @param pad_index Which pad to set attributes for.
 * @param attrs Attribute bits, written directly to attribute field.
 * @return dif_padctrl_change_attr_result_t
 */
dif_padctrl_change_attr_result_t dif_padctrl_write_attrs(
    const dif_padctrl_t *padctrl, dif_padctrl_pad_kind_t kind,
    dif_padctrl_pad_index_t index, dif_padctrl_attr_t attrs);

/**
 * Get attributes for a pad.
 *
 * @param padctrl Padctrl state data.
 * @param pad_kind Which kind of pad to get attributes for.
 * @param pad_index Which pad to get attributes for.
 * @param attrs_out Out parameter for the attributes read.
 * @return dif_padctrl_result_t
 */
dif_padctrl_result_t dif_padctrl_get_attrs(const dif_padctrl_t *padctrl,
                                           dif_padctrl_pad_kind_t kind,
                                           dif_padctrl_pad_index_t index,
                                           dif_padctrl_attr_t *attrs_out);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PADCTRL_H_
