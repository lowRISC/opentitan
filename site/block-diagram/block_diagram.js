/* Copyright lowRISC contributors (OpenTitan project).
 * Licensed under the Apache License, Version 2.0, see LICENSE for details.
 * SPDX-License-Identifier: Apache-2.0
 */

/**
 * Fetch the latest stats for a block diagram and add them as tooltips.
 *
 * @param {string} statsURL URL to the JSON stats report file for this block diagram.
 * @param {Array} blocks Collection of HTMLElements for the block-diagram's blocks.
 */
async function loadTooltips(statsURL, blocks) {
    // Fetch the latest stats report.
    const req = new XMLHttpRequest();
    req.onload = (event) => {
        const stats = JSON.parse(req.response);
        // Assign data to each block.
        for (block of blocks) {
            const tooltip = buildTooltip(stats[block.id]);
            block.appendChild(tooltip);
        }
    };
    req.open("GET", statsURL, true);
    req.send();
}
/*

/**
 * Build a tooltip HTML element.
 *
 * Currently always builds the EDN elements. Would like it to take JSON for the
 * parameters.
 *
 * @param {Object} stats Stats for this block with these properties:
 *     * name
 *     * version
 *     * design_stage (may be null)
 *     * verification_stage (may be null)
 *     * total_runs (may be null)
 *     * total_passing (may be null)
 * @returns {HTMLElement} Tooltip element built from the given stats.
 */
function buildTooltip(stats) {
    let name = stats.name;
    // Add version to the block's name if available.
    if (stats.version != null) {
        name += ` v${stats.version}`;
    }

    // Start collecting child elements of the tooltip.
    let children = [
        buildElement("p", "tooltip-title", name),
    ];

    // Append the design and verification stages if the block has them.
    if (stats.design_stage && stats.verification_stage) {
        // Get status classes for design and verification stages.
        const design_status = getStageStatus(stats.design_stage);
        const verification_status = getStageStatus(stats.verification_stage);

        children = children.concat([
            buildElement(
                "span",
                `value status ${design_status}`,
                stats.design_stage
            ),
            buildElement("span", "label", "design"),
            buildElement(
                "span",
                `value status ${verification_status}`,
                stats.verification_stage
            ),
            buildElement("span", "label", "verification"),
        ]);
    }

    // Append test status if the block has it.
    if (stats.total_runs && stats.total_passing) {
        // Calculate passing percentage and status class.
        const passing = Math.floor(
            100 * stats.total_passing / stats.total_runs
        );
        const passing_status = getPassingStatus(passing);

        children = children.concat([
            buildElement("hr"),
            buildElement("span", "value", stats.total_runs),
            buildElement("span", "label", "tests"),
            buildElement(
                "span",
                `value percentage ${passing_status}`,
                `${passing}%`
            ),
            buildElement("span", "label", "passing"),
        ]);
    }

    let tooltip = document.createElement("div");
    tooltip.className = "tooltip";

    for (child of children) {
        tooltip.appendChild(child);
    }

    return tooltip;
}

/**
 * Convenience function to build an element with the given classes and content.
 *
 * @param {string} tag The HTML tag, e.g. "span".
 * @param {string} classes Space-separated classes.
 * @param {string} content Text content to go inside the element.
 * @returns {HTMLElement} Constructed element.
 */
function buildElement(tag, classes = "", content = "") {
    let element = document.createElement(tag);
    element.className = classes;
    element.textContent = content;
    return element;
}

/**
 * Gets the `status[1234]` class for a design or verification stage.
 *
 * @param {string} stage A design or verification stage, or "N/A".
 * @returns {string} The `status[1234]` class corresponding to this stage.
 */
function getStageStatus(stage) {
    switch (stage) {
        case "N/A":
            return "";
        case "D0":
        case "V0":
            return "status1";
        case "D1":
        case "V1":
            return "status2";
        case "D2":
        case "V2":
        case "D2S":
        case "V2S":
            return "status3";
        case "D3":
        case "V3":
            return "status4";
        default:
            throw `unknown stage "${stage}"`;
    }
}

/**
 * Gets the `status[1234]` class for a passing-rate percentage.
 *
 * @param {number} passing Percentage in [0, 100] of how many tests are passing.
 * @returns {string} The `status[1234]` class corresponding to this percentage.
 */
function getPassingStatus(passing) {
    if (passing < 50) {
        return "status1";
    } else if (passing <= 90) {
        return "status2";
    } else if (passing < 100) {
        return "status3";
    } else if (passing == 100) {
        return "status4";
    } else {
        throw `invalid passing percentage "${passing}"`
    }
}
