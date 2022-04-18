// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SENSOR_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SENSOR_CTRL_H_

/**
 * @file
 * @brief <a href="/hw/top_earlgrey/ip/sensor_ctrl/doc/">Sensor Controller</a>
 * Device Interface Functions
 */

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_sensor_ctrl_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * An event, identified by a numeric id.
 *
 */
typedef uint32_t dif_sensor_ctrl_event_idx_t;

/**
 * A vector of AST events, where each bit represents one event.
 *
 */
typedef uint32_t dif_sensor_ctrl_events_t;

/**
 * IO power status
 * Each bit represents the current status of a particular IO rail.
 *
 */
typedef uint32_t dif_sensor_ctrl_io_power_status_t;

/**
 * Locks sensor control configuration from further updates.
 *
 *
 * @param sensor_ctrl A sensor_ctrl handle.
 * @return 'kDifBadArg' if `handle` is null.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sensor_ctrl_lock_cfg(const dif_sensor_ctrl_t *sensor_ctrl);

/**
 * Sets the value for a particular AST event trigger.
 *
 * @param sensor_ctrl A sensor_ctrl handle.
 * @param event_idx The event to configure.
 * @return 'kDifBadArg' if `handle` is null or if `event_idx` is larger than the
 * number of events supported.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sensor_ctrl_set_ast_event_trigger(
    const dif_sensor_ctrl_t *sensor_ctrl, dif_sensor_ctrl_event_idx_t event_idx,
    dif_toggle_t enable);

/**
 * Sets the fatality configuration of a particular event.
 *
 * An event can be configured to be either fatal or recoverable.
 *
 * @param sensor_ctrl A sensor_ctrl handle.
 * @param en_fatal The fatality enablement state of an event. If
 * `kDifToggleEnabled`, the event is fatal.  Otherwise, it is recoverable.
 * @param event_idx The event to configure
 * @return 'kDifBadArg' if `handle` is null or `event_idx` is larger than the
 * number of events supported.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sensor_ctrl_set_alert_fatal(
    const dif_sensor_ctrl_t *sensor_ctrl, dif_sensor_ctrl_event_idx_t event_idx,
    dif_toggle_t en_fatal);

/**
 * Gets the current vector of recoverable events.
 *
 * @param sensor_ctrl A sensor_ctrl handle.
 * @param[out] events The set of current recoverable events
 * @return 'kDifBadArg' if `handle` is null.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sensor_ctrl_get_recov_events(
    const dif_sensor_ctrl_t *sensor_ctrl, dif_sensor_ctrl_events_t *events);

/**
 * Clears the specified recoverable events.
 *
 * @param sensor_ctrl A sensor_ctrl handle.
 * @param event_idx The event to clear.
 * @return 'kDifBadArg' if `handle` is null or 'event_idx' is larger than the
 * number of events supported..
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sensor_ctrl_clear_recov_event(
    const dif_sensor_ctrl_t *sensor_ctrl,
    dif_sensor_ctrl_event_idx_t event_idx);

/**
 * Gets the current vector of fatal events.
 *
 * @param sensor_ctrl A sensor_ctrl handle.
 * @param[out] events The set of current fatal events.
 * @return 'kDifBadArg' if `handle` is null.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sensor_ctrl_get_fatal_events(
    const dif_sensor_ctrl_t *sensor_ctrl, dif_sensor_ctrl_events_t *events);

/**
 * Gets the current ast init done status.
 *
 * @param sensor_ctrl A sensor_ctrl handle.
 * @param[out] done Current init_done status.
 * @return 'kDifBadArg' if `handle` is null.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sensor_ctrl_get_ast_init_done_status(
    const dif_sensor_ctrl_t *sensor_ctrl, dif_toggle_t *done);

/**
 * Gets the current io power status.
 *
 * @param sensor_ctrl A sensor_ctrl handle.
 * @param[out] done Current io power status.
 * @return 'kDifBadArg' if `handle` is null.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sensor_ctrl_get_io_power_status(
    const dif_sensor_ctrl_t *sensor_ctrl,
    dif_sensor_ctrl_io_power_status_t *io_status);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SENSOR_CTRL_H_
