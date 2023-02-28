// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

import metadata from "./metadata.js";
import metrics from "./metrics.js";

const hostname = "<<<HOSTNAME>>>";

const BADGE_MAP = {
    "D0": "alert",
    "D1": "warn",
    "D2": "prettygood",
    "D2S": "prettygood",
    "D3": "good",
    "V0": "alert",
    "V1": "warn",
    "V2": "prettygood",
    "V2S": "prettygood",
    "V3": "good",
}

async function parseMetrics(id) {
    if (!metrics[id]) return null;
    return metrics[id].revisions.slice(-1)[0];
}

async function parseReport(path) {
    if (!path || path === "TODO") return null;

    try {
        const response = await fetch(`https://reports.opentitan.org${path}/latest/report.json`, {
            mode: "no-cors"
        });
        if (response.status < 200 || response.status >= 300) return null;
        const report = await response.json();

        console.log(report);

        const total = report.results.testpoints
            .flatMap(t => t.tests)
            .concat(report.results.unmapped_tests)
            .filter((t, i, a) => a.findIndex(o => o.name === t.name) === i)
            .map(t => t.total_runs)
            .reduce((acc, x) => acc + x, 0);

        const passing = report.results.testpoints
            .flatMap(t => t.tests)
            .concat(report.results.unmapped_tests)
            .filter((t, i, a) => a.findIndex(o => o.name === t.name) === i)
            .map(t => t.passing_runs)
            .reduce((acc, x) => acc + x, 0);

        return {
            tests: { passing, total }
        };
    } catch (e) {
        console.error(`no report for ${path}`, e);
        return null;
    }
}

async function hydrate() {
    await Promise.all(Object.entries(metadata).map(async ([key, data], tabIndex) => {
        const element = document.getElementById(key);

        const focusable = document.createElement("div");
        element.appendChild(focusable);
        focusable.classList.add("block-focus");

        let status = await parseMetrics(data.metrics);
        let report = await parseReport(data.report);

        if (data.report && data.report != "TODO" && !report) {
            console.warn(`No report for ${key} (${data.report})`, data);
        }

        const tooltip = document.createElement("div");
        tooltip.classList.add("diagram-tooltip");

        const tooltip_box = document.createElement("div");
        tooltip_box.classList.add("tooltip-box");
        tooltip_box.innerHTML = `
            <span class="tooltip-title">
                ${data.title.toUpperCase()}${status ? ` v${status.version}` : ""}
            </span>
        `;

        tooltip.appendChild(tooltip_box);

        element.appendChild(tooltip);
        element.classList.add("has-tooltip");
        focusable.tabIndex = tabIndex + 1;

        if (status) {
            tooltip_box.innerHTML += `
                <span class="tooltip-value tooltip-badge tooltip-badge-${BADGE_MAP[status.design_stage] || "none"}">
                    ${status.design_stage}
                </span>
                <span class="tooltip-label">
                    design
                </span>
                <span class="tooltip-value tooltip-badge tooltip-badge-${BADGE_MAP[status.verification_stage] || "none"}">
                    ${status.verification_stage}
                </span>
                <span class="tooltip-label">
                    verification
                </span>
            `;
        }

        if (report && status) {
            tooltip_box.innerHTML += `
                <span class="tooltip-divider"></span>
            `;
        }

        if (report) {
            const rate = Math.floor(20 * report.tests.passing / report.tests.total) * 5;
            tooltip_box.classList.add("has-report");
            tooltip_box.innerHTML += `
                <span class="tooltip-value">
                    ${report.tests.total}
                </span>
                <span class="tooltip-label">
                    tests
                </span>
                <span class="tooltip-value tooltip-report-tests rate-${rate}">
                    ${Math.floor(100 * report.tests.passing / report.tests.total)}%
                </span>
                <span class="tooltip-label">
                    passing
                </span>
            `;
        }

        if (data.href) {
            const link = document.createElement("a");
            link.href = hostname + data.href;

            link.style.display = "contents";
            element.parentElement.appendChild(link);
            link.appendChild(element);
        }
    }));

    document.getElementById("hydrate").remove();
    document.getElementById("custom-elements").remove();

    return true;
}

window.hydrated = hydrate();
