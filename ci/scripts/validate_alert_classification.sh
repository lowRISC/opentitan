#!/usr/bin/env bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Script to validate that the number of values in alert classification arrays
# matches the number of alerts in the alert handler configuration
# Usage: ./validate_alert_classification.sh <alert_handler_ipconfig.hjson> <owner_sw_cfg.hjson>

set -e

# Check arguments
if [ $# -ne 2 ]; then
    echo "Usage: $0 <alert_handler_ipconfig.hjson> <owner_sw_cfg.hjson>"
    echo "  alert_handler_ipconfig.hjson: Alert handler configuration file"
    echo "  owner_sw_cfg.hjson: Owner SW configuration file"
    exit 1
fi

ALERT_HANDLER_FILE="$1"
OWNER_SW_CFG_FILE="$2"

# Check if files exist
if [ ! -f "$ALERT_HANDLER_FILE" ]; then
    echo "Error: Alert handler file '$ALERT_HANDLER_FILE' not found"
    exit 1
fi

if [ ! -f "$OWNER_SW_CFG_FILE" ]; then
    echo "Error: Owner SW config file '$OWNER_SW_CFG_FILE' not found"
    exit 1
fi

echo "Extracting alert counts from alert handler..."

# Use grep to extract n_alerts since it's HJSON format
ALERT_COUNT=$(grep 'n_alerts:' "$ALERT_HANDLER_FILE" | sed 's/.*n_alerts: *\([0-9]*\).*/\1/')
LOC_ALERT_COUNT=$(grep 'n_loc_alert:' "$ALERT_HANDLER_FILE" | sed 's/.*n_loc_alert: *\([0-9]*\).*/\1/')

if [ -z "$ALERT_COUNT" ] || ! [[ "$ALERT_COUNT" =~ ^[0-9]+$ ]]; then
    echo "Error: Could not extract n_alerts from alert handler config"
    exit 1
fi

if [ -z "$LOC_ALERT_COUNT" ] || ! [[ "$LOC_ALERT_COUNT" =~ ^[0-9]+$ ]]; then
    echo "Error: Could not extract n_loc_alert from alert handler config"
    exit 1
fi

echo "   Alert handler has $ALERT_COUNT alerts"
echo "   Alert handler has $LOC_ALERT_COUNT local alerts"

echo "Extracting classification counts from owner SW config..."

# Count the number of values in the OWNER_SW_CFG_ROM_ALERT_CLASSIFICATION array
# Use line numbers to be more precise
START_LINE=$(grep -n 'name: "OWNER_SW_CFG_ROM_ALERT_CLASSIFICATION"' "$OWNER_SW_CFG_FILE" | cut -d: -f1)
END_LINE=$(grep -n 'name: "OWNER_SW_CFG_ROM_LOCAL_ALERT_CLASSIFICATION"' "$OWNER_SW_CFG_FILE" | cut -d: -f1)

if [ -z "$START_LINE" ] || [ -z "$END_LINE" ]; then
    echo "Error: Could not find classification section boundaries"
    exit 1
fi

# Extract the range and count hex values for regular alerts
CLASSIFICATION_COUNT=$(sed -n "${START_LINE},${END_LINE}p" "$OWNER_SW_CFG_FILE" | \
                       grep -c '"0x' || echo "0")

if [ "$CLASSIFICATION_COUNT" -eq 0 ]; then
    echo "Error: Could not find or count OWNER_SW_CFG_ROM_ALERT_CLASSIFICATION values"
    exit 1
fi

echo "   Owner SW config has $CLASSIFICATION_COUNT alert classification values"

# Count the number of values in the OWNER_SW_CFG_ROM_LOCAL_ALERT_CLASSIFICATION array
LOCAL_START_LINE=$(grep -n 'name: "OWNER_SW_CFG_ROM_LOCAL_ALERT_CLASSIFICATION"' "$OWNER_SW_CFG_FILE" | cut -d: -f1)
LOCAL_END_LINE=$(grep -n 'name: "OWNER_SW_CFG_ROM_ALERT_ACCUM_THRESH"' "$OWNER_SW_CFG_FILE" | cut -d: -f1)

if [ -z "$LOCAL_START_LINE" ] || [ -z "$LOCAL_END_LINE" ]; then
    echo "Error: Could not find local alert classification section boundaries"
    exit 1
fi

# Extract the range and count hex values for local alerts
LOCAL_CLASSIFICATION_COUNT=$(sed -n "${LOCAL_START_LINE},${LOCAL_END_LINE}p" "$OWNER_SW_CFG_FILE" | \
                             grep -c '"0x' || echo "0")

if [ "$LOCAL_CLASSIFICATION_COUNT" -eq 0 ]; then
    echo "Error: Could not find or count OWNER_SW_CFG_ROM_LOCAL_ALERT_CLASSIFICATION values"
    exit 1
fi

echo "   Owner SW config has $LOCAL_CLASSIFICATION_COUNT local alert classification values"

echo ""
echo "   Validation Results:"
echo "   Alert Handler Alerts: $ALERT_COUNT"
echo "   Alert Classification Values: $CLASSIFICATION_COUNT"
echo "   Alert Handler Local Alerts: $LOC_ALERT_COUNT"
echo "   Local Alert Classification Values: $LOCAL_CLASSIFICATION_COUNT"

# Compare the counts
ALERT_MATCH=false
LOCAL_ALERT_MATCH=false

if [ "$ALERT_COUNT" -eq "$CLASSIFICATION_COUNT" ]; then
    ALERT_MATCH=true
fi

if [ "$LOC_ALERT_COUNT" -eq "$LOCAL_CLASSIFICATION_COUNT" ]; then
    LOCAL_ALERT_MATCH=true
fi

if [ "$ALERT_MATCH" = true ] && [ "$LOCAL_ALERT_MATCH" = true ]; then
    echo ""
    echo "   SUCCESS: All alert counts match classification counts!"
    echo "   Regular alerts: $ALERT_COUNT items"
    echo "   Local alerts: $LOC_ALERT_COUNT items"
    exit 0
else
    echo ""
    echo "   MISMATCH: Alert counts do not match classification counts!"
    if [ "$ALERT_MATCH" = false ]; then
        echo "   Regular alerts: handler has $ALERT_COUNT, config has $CLASSIFICATION_COUNT"
    fi
    if [ "$LOCAL_ALERT_MATCH" = false ]; then
        echo "   Local alerts: handler has $LOC_ALERT_COUNT, config has $LOCAL_CLASSIFICATION_COUNT"
    fi
    exit 1
fi
