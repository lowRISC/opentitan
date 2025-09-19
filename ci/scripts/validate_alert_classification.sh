#!/usr/bin/env bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Script to validate that the number of values in alert classification arrays
# matches the number of alerts in the alert handler configuration
# and validate/update digest values
# Usage: ./validate_alert_classification.sh [--update] <alert_handler_ipconfig.hjson> <owner_sw_cfg.hjson>

set -e

# =============================================================================
# FUNCTIONS
# =============================================================================

# Function to count classification values in a section
count_classification_values() {
    local start_name="$1"
    local end_name="$2"
    local section_type="$3"
    local file="$4"

    # Find start and end line numbers
    local start_line
    start_line=$(grep -n "name: \"$start_name\"" "$file" | cut -d: -f1)
    local end_line
    end_line=$(grep -n "name: \"$end_name\"" "$file" | cut -d: -f1)

    if [ -z "$start_line" ] || [ -z "$end_line" ]; then
        echo "Error: Could not find $section_type classification section boundaries"
        exit 1
    fi

    # Extract the range and count hex values
    local count
    count=$(sed -n "${start_line},${end_line}p" "$file" | grep -c '"0x' || echo "0")

    if [ "$count" -eq 0 ]; then
        echo "Error: Could not find or count $start_name values"
        exit 1
    fi

    echo "$count"
}

decimal_to_hex() {
    printf "0x%x" "$1"
}

# Function to extract digest value from owner_sw_cfg.hjson
extract_digest_value() {
    local digest_name="$1"
    local file="$2"
    grep -A 1 "name: \"$digest_name\"" "$file" | grep "value:" | sed 's/.*value: "0x\([0-9a-fA-F]*\)".*/\1/'
}

# Function to update digest value in owner_sw_cfg.hjson
update_digest_value() {
    local digest_name="$1"
    local new_hex_value="$2"
    local file="$3"
    local temp_file
    temp_file=$(mktemp)

    # Update the value using sed
    sed "/name: \"$digest_name\"/,/value: \"0x[0-9a-fA-F]*\"/s/value: \"0x[0-9a-fA-F]*\"/value: \"$new_hex_value\"/" "$file" > "$temp_file"
    mv "$temp_file" "$file"
}

validate_alert_classification() {
    local alert_handler_file="$1"
    local owner_sw_cfg_file="$2"

    echo "=== Alert Classification Validation ==="
    echo "Extracting alert counts from alert handler..."
    local alert_count
    alert_count=$(grep 'n_alerts:' "$alert_handler_file" | sed 's/.*n_alerts: *\([0-9]*\).*/\1/')
    local loc_alert_count
    loc_alert_count=$(grep 'n_loc_alert:' "$alert_handler_file" | sed 's/.*n_loc_alert: *\([0-9]*\).*/\1/')

    if [ -z "$alert_count" ] || ! [[ "$alert_count" =~ ^[0-9]+$ ]]; then
        echo "Error: Could not extract n_alerts from alert handler config"
        return 1
    fi

    if [ -z "$loc_alert_count" ] || ! [[ "$loc_alert_count" =~ ^[0-9]+$ ]]; then
        echo "Error: Could not extract n_loc_alert from alert handler config"
        return 1
    fi

    echo "   Alert handler has $alert_count alerts"
    echo "   Alert handler has $loc_alert_count local alerts"

    echo "Extracting classification counts from owner SW config..."

    # Count regular alert classification values
    local classification_count
    classification_count=$(count_classification_values \
        "OWNER_SW_CFG_ROM_ALERT_CLASSIFICATION" \
        "OWNER_SW_CFG_ROM_LOCAL_ALERT_CLASSIFICATION" \
        "alert" \
        "$owner_sw_cfg_file")

    echo "   Owner SW config has $classification_count alert classification values"

    # Count local alert classification values
    local local_classification_count
    local_classification_count=$(count_classification_values \
        "OWNER_SW_CFG_ROM_LOCAL_ALERT_CLASSIFICATION" \
        "OWNER_SW_CFG_ROM_ALERT_ACCUM_THRESH" \
        "local alert" \
        "$owner_sw_cfg_file")

    echo "   Owner SW config has $local_classification_count local alert classification values"

    # Compare the counts
    local alert_match=false
    local local_alert_match=false

    if [ "$alert_count" -eq "$classification_count" ]; then
        alert_match=true
    fi

    if [ "$loc_alert_count" -eq "$local_classification_count" ]; then
        local_alert_match=true
    fi

    echo ""
    echo "   Alert Classification Results:"
    echo "   Alert Handler Alerts: $alert_count"
    echo "   Alert Classification Values: $classification_count"
    echo "   Alert Handler Local Alerts: $loc_alert_count"
    echo "   Local Alert Classification Values: $local_classification_count"

    if [ "$alert_match" = true ] && [ "$local_alert_match" = true ]; then
        echo ""
        echo "SUCCESS: Alert classification validation passed!"
        echo "   Regular alerts: $alert_count items"
        echo "   Local alerts: $loc_alert_count items"
        return 0
    else
        echo ""
        echo "ALERT CLASSIFICATION VALIDATION FAILED:"
        if [ "$alert_match" = false ]; then
            echo "   Regular alerts: handler has $alert_count, config has $classification_count"
        fi
        if [ "$local_alert_match" = false ]; then
            echo "   Local alerts: handler has $loc_alert_count, config has $local_classification_count"
        fi
        return 1
    fi
}

validate_digest_values() {
    local alert_handler_file="$1"
    local owner_sw_cfg_file="$2"

    local digest_match=true
    echo ""
    echo "=== Digest Validation ==="
    echo "Validating digest values..."

    # Extract current digest values from owner_sw_cfg.hjson
    local current_prod_hex
    current_prod_hex=$(extract_digest_value "OWNER_SW_CFG_ROM_ALERT_DIGEST_PROD" "$owner_sw_cfg_file")
    local current_prod_end_hex
    current_prod_end_hex=$(extract_digest_value "OWNER_SW_CFG_ROM_ALERT_DIGEST_PROD_END" "$owner_sw_cfg_file")
    local current_dev_hex
    current_dev_hex=$(extract_digest_value "OWNER_SW_CFG_ROM_ALERT_DIGEST_DEV" "$owner_sw_cfg_file")
    local current_rma_hex
    current_rma_hex=$(extract_digest_value "OWNER_SW_CFG_ROM_ALERT_DIGEST_RMA" "$owner_sw_cfg_file")

    if [ -z "$current_prod_hex" ] || [ -z "$current_prod_end_hex" ] || [ -z "$current_dev_hex" ] || [ -z "$current_rma_hex" ]; then
        echo "Error: Could not extract digest values from owner SW config"
        return 1
    fi

    echo "   Current digest values:"
    echo "     PROD: 0x$current_prod_hex"
    echo "     PROD_END: 0x$current_prod_end_hex"
    echo "     DEV: 0x$current_dev_hex"
    echo "     RMA: 0x$current_rma_hex"

    echo "   Generating expected digest values using opentitantool..."

    # Use the provided files directly
    # Construct path to alert_handler.hjson (not ipconfig.hjson) for regtool.py
    local alert_handler_regtool_file
    alert_handler_regtool_file=$(dirname "$alert_handler_file")/alert_handler.hjson

    if [ ! -f "$alert_handler_regtool_file" ]; then
        echo "Error: Alert handler file for regtool '$alert_handler_regtool_file' not found"
        return 1
    fi

    # Generate the alert handler registers for the selected top
    echo "   Generating alert handler registers..."
    ./util/regtool.py "$alert_handler_regtool_file" -R -o "sw/host/opentitanlib/src/otp/alert_handler_regs.rs"

    # Run opentitantool to get expected digest values
    echo "   Running opentitantool to calculate expected digest values..."
    echo "   Command: bazel run //sw/host/opentitantool -- --rcfile=\"\" otp alert-digest \"$(realpath "$owner_sw_cfg_file")\""
    local expected_digests
    expected_digests=$(timeout 300 bazel run //sw/host/opentitantool -- --rcfile="" otp alert-digest "$(realpath "$owner_sw_cfg_file")" 2>&1)

    # Clean up generated file to avoid git diff
    git checkout -- "sw/host/opentitanlib/src/otp/alert_handler_regs.rs" >/dev/null 2>&1

    if [ -z "$expected_digests" ]; then
        echo "Error: Failed to generate expected digest values"
        return 1
    fi

    # Extract expected values from the HJSON output (handles the actual format)
    local expected_prod_decimal
    expected_prod_decimal=$(echo "$expected_digests" | grep -A 2 'name: "OWNER_SW_CFG_ROM_ALERT_DIGEST_PROD"' | grep 'value:' | sed 's/.*value: *\([0-9]*\).*/\1/')
    local expected_prod_end_decimal
    expected_prod_end_decimal=$(echo "$expected_digests" | grep -A 2 'name: "OWNER_SW_CFG_ROM_ALERT_DIGEST_PROD_END"' | grep 'value:' | sed 's/.*value: *\([0-9]*\).*/\1/')
    local expected_dev_decimal
    expected_dev_decimal=$(echo "$expected_digests" | grep -A 2 'name: "OWNER_SW_CFG_ROM_ALERT_DIGEST_DEV"' | grep 'value:' | sed 's/.*value: *\([0-9]*\).*/\1/')
    local expected_rma_decimal
    expected_rma_decimal=$(echo "$expected_digests" | grep -A 2 'name: "OWNER_SW_CFG_ROM_ALERT_DIGEST_RMA"' | grep 'value:' | sed 's/.*value: *\([0-9]*\).*/\1/')

    if [ -z "$expected_prod_decimal" ] || [ -z "$expected_prod_end_decimal" ] || [ -z "$expected_dev_decimal" ] || [ -z "$expected_rma_decimal" ]; then
        echo "Error: Could not extract expected digest values from opentitantool output"
        echo "Full output was:"
        echo "$expected_digests"
        return 1
    fi

    local expected_prod_hex
    expected_prod_hex=$(decimal_to_hex "$expected_prod_decimal")
    local expected_prod_end_hex
    expected_prod_end_hex=$(decimal_to_hex "$expected_prod_end_decimal")
    local expected_dev_hex
    expected_dev_hex=$(decimal_to_hex "$expected_dev_decimal")
    local expected_rma_hex
    expected_rma_hex=$(decimal_to_hex "$expected_rma_decimal")

    echo "   Expected digest values:"
    echo "     PROD: $expected_prod_hex ($expected_prod_decimal)"
    echo "     PROD_END: $expected_prod_end_hex ($expected_prod_end_decimal)"
    echo "     DEV: $expected_dev_hex ($expected_dev_decimal)"
    echo "     RMA: $expected_rma_hex ($expected_rma_decimal)"

    # Compare digest values
    if [ "0x$current_prod_hex" != "$expected_prod_hex" ]; then
        digest_match=false
    fi
    if [ "0x$current_prod_end_hex" != "$expected_prod_end_hex" ]; then
        digest_match=false
    fi
    if [ "0x$current_dev_hex" != "$expected_dev_hex" ]; then
        digest_match=false
    fi
    if [ "0x$current_rma_hex" != "$expected_rma_hex" ]; then
        digest_match=false
    fi

    echo ""
    echo "   Digest Validation Results:"
    echo "   Digest Values Match: $([ "$digest_match" = true ] && echo "YES" || echo "NO")"

    # Store results in global variables for use by perform_update()
    DIGEST_MATCH="$digest_match"
    EXPECTED_PROD_HEX="$expected_prod_hex"
    EXPECTED_PROD_END_HEX="$expected_prod_end_hex"
    EXPECTED_DEV_HEX="$expected_dev_hex"
    EXPECTED_RMA_HEX="$expected_rma_hex"

    if [ "$digest_match" = true ]; then
        echo ""
        echo "SUCCESS: Digest validation passed!"
        echo "   Digest values: All match expected values"
        return 0
    else
        echo ""
        echo "DIGEST VALIDATION FAILED:"
        echo "   Digest values: Current values do not match expected values"
        echo "   Use --update flag to automatically update digest values"
        return 1
    fi
}

perform_update() {
    local owner_sw_cfg_file="$1"

    echo ""
    echo "Update mode enabled..."

    if [ "$DIGEST_MATCH" = false ]; then
        echo "   Updating digest values..."
        update_digest_value "OWNER_SW_CFG_ROM_ALERT_DIGEST_PROD" "$EXPECTED_PROD_HEX" "$owner_sw_cfg_file"
        update_digest_value "OWNER_SW_CFG_ROM_ALERT_DIGEST_PROD_END" "$EXPECTED_PROD_END_HEX" "$owner_sw_cfg_file"
        update_digest_value "OWNER_SW_CFG_ROM_ALERT_DIGEST_DEV" "$EXPECTED_DEV_HEX" "$owner_sw_cfg_file"
        update_digest_value "OWNER_SW_CFG_ROM_ALERT_DIGEST_RMA" "$EXPECTED_RMA_HEX" "$owner_sw_cfg_file"
        echo "   SUCCESS: Digest values updated successfully!"
    else
        echo "   SUCCESS: Digest values are already correct, no update needed"
    fi
}

# =============================================================================
# MAIN SCRIPT
# =============================================================================

UPDATE_MODE=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --update)
            UPDATE_MODE=true
            shift
            ;;
        *)
            if [ -z "$ALERT_HANDLER_FILE" ]; then
                ALERT_HANDLER_FILE="$1"
            elif [ -z "$OWNER_SW_CFG_FILE" ]; then
                OWNER_SW_CFG_FILE="$1"
            else
                echo "Error: Too many arguments"
                exit 1
            fi
            shift
            ;;
    esac
done

if [ -z "$ALERT_HANDLER_FILE" ] || [ -z "$OWNER_SW_CFG_FILE" ]; then
    echo "Usage: $0 [--update] <alert_handler_ipconfig.hjson> <owner_sw_cfg.hjson>"
    echo "  --update: Update the digest values in the owner_sw_cfg.hjson file"
    echo "  alert_handler_ipconfig.hjson: Alert handler configuration file"
    echo "  owner_sw_cfg.hjson: Owner SW configuration file"
    echo "  Note: Top name is automatically detected from file paths"
    exit 1
fi

# Check if files exist
if [ ! -f "$ALERT_HANDLER_FILE" ]; then
    echo "Error: Alert handler file '$ALERT_HANDLER_FILE' not found"
    exit 1
fi

if [ ! -f "$OWNER_SW_CFG_FILE" ]; then
    echo "Error: Owner SW config file '$OWNER_SW_CFG_FILE' not found"
    exit 1
fi

if ! validate_alert_classification "$ALERT_HANDLER_FILE" "$OWNER_SW_CFG_FILE"; then
    echo ""
    echo "ERROR: Alert classification validation failed!"
    exit 1
fi

if ! validate_digest_values "$ALERT_HANDLER_FILE" "$OWNER_SW_CFG_FILE"; then
    # If digest validation failed and we're in update mode, perform updates
    if [ "$UPDATE_MODE" = true ]; then
        perform_update "$OWNER_SW_CFG_FILE"

        # Perform post-update digest validation only
        echo ""
        if validate_digest_values "$ALERT_HANDLER_FILE" "$OWNER_SW_CFG_FILE"; then
            echo ""
            echo "SUCCESS: All validations passed after update!"
            exit 0
        else
            echo ""
            echo "ERROR: Digest validation still failed after update!"
            exit 1
        fi
    else
        echo ""
        echo "ERROR: Digest validation failed!"
        exit 1
    fi
else
    echo ""
    echo "SUCCESS: All validations passed!"
    exit 0
fi
