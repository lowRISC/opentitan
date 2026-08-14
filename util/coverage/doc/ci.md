# CI Testing

This document describes the host-side infrastructure for capturing, processing,
and aggregating OpenTitan coverage data. The system is integrated into the
Continuous Integration (CI) pipeline to ensure consistent and authoritative
coverage reporting for the entire project.

The host-side processing involves two primary stages:

1.  **Collection:** Raw coverage data is captured from individual test
    executions and consolidated into job-specific artifacts.
2.  **Aggregation:** Data from all test parallel executions is merged,
    normalized, and processed to generate unified reports.

## CI Workflows

OpenTitan employs two primary CI coverage workflows:

-   **Presubmit (Quick Coverage):** Coverage collection for every pull request.
    It focuses on a subset of fast-executing tests, specifically those that run
    on the host PC or within simulators (e.g., `otbnsim` or QEMU). FPGA-based
    tests are skipped in this workflow to ensure quick feedback.
-   **Nightly (Full Coverage):** A comprehensive nightly run that executes the
    entire test suite with coverage enabled across all supported platforms (FPGA
    and QEMU). This run generates the authoritative coverage reports used for
    certification and quality tracking.

## Smoke Tests

To ensure the technical correctness of the coverage collection pipeline, the
project includes a suite of specialized
[Smoke Tests](../../../sw/device/lib/coverage/smoke/README.md). These tests
verify that coverage is correctly reported across different languages (C, ASM,
OTBN) and environments (Unit Test, E2E, Simulation).

The **Presubmit** workflow relies on these smoke tests to provide fast
validation of the coverage infrastructure.

## Known Issues and Exclusions

To maintain stability in the coverage pipeline, some tests may be temporarily
excluded from collection.

-   **`coverage_broken` tag:** Any test target annotated with the
    `coverage_broken` tag is automatically skipped by the repository-wide
    coverage discovery scripts. This tag is used for tests that are known to be
    incompatible with the coverage framework.

## Collection & Merging Pipeline

The coverage data lifecycle on the host is managed by two primary scripts. In
OpenTitan's CI environment, tests are split into multiple shards and executed in
parallel across many executors. These scripts are designed to coordinate
coverage collection across this distributed infrastructure:

-   **Collection:** The `collect-coverage-report.sh` script runs on each
    individual executor. It gathers all coverage artifacts for its specific CI
    action into a dedicated folder, preparing them for upload as intermediate
    executor artifacts.

-   **Merging & Publishing:** After all test executors have finished, a separate
    "publish" CI action begins. This action downloads all intermediate artifacts
    and invokes the `merge-coverage-report.sh` script to combine them into a
    single, comprehensive repository-wide report.

These scripts can also be run manually to generate a local report:

```bash
# 1. Run the tests with coverage enabled
./bazelisk.sh coverage --config=ot_coverage <test_targets...> [<view_targets>...]

# 2. Collect coverage result and artifacts
# (The collection directory defaults to /tmp/$USER/coverage_report.)
bash ci/scripts/collect-coverage-report.sh [collect_dir]

# 3. Merge artifacts and generate the final report
# (The output directory defaults to /tmp/$USER/merged_coverage.)
bash ci/scripts/merge-coverage-report.sh [collect_dir] [output_dir]
```

### `collect-coverage-report.sh`

This script runs at the conclusion of individual CI actions. It gathers all
artifacts necessary for global aggregation:

1.  **Coverage Data Collection:** Gathers all coverage data (LCOV files and
    metadata) from the tests executed on the executor.
2.  **Log Collection:** Gathers `test.xml` results for all tests processed.
3.  **Source Extraction:** Identifies all source files referenced in the LCOV
    data and captures them to ensure they are available for final report
    generation.

### `merge-coverage-report.sh`

This script runs after all CI actions have completed. It:

1.  **Global Merging:** Combines artifacts from all parallel CI executors into a
    single repository-wide dataset.
2.  **Data Normalization:** Normalizes static inline function names and path
    prefixes for generated files to ensure a consistent report.
3.  **Report Generation:** Produces coverage reports and artifacts for
    publishing.
