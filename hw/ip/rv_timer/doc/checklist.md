---
title: "RV_TIMER Checklist"
---

This checklist is for [Hardware Stage]({{<relref "/doc/project/development_stages.md" >}})
transitions for the [rv_timer peripheral.](../) All checklist
items refer to the content in the [Checklist.]({{<relref "/doc/project/checklist.md" >}})

## Design Checklist

### D1

Type          | Item                  | Resolution  | Note/Collaterals
--------------|-----------------------|-------------|------------------
Documentation | [SPEC_COMPLETE][]     | Done        | [RV_TIMER Spec][]
Documentation | [CSR_DEFINED][]       | Done        |
RTL           | [CLKRST_CONNECTED][]  | Done        |
RTL           | [IP_TOP][]            | Done        |
RTL           | [IP_INSTANTIABLE][]      | Done        |
RTL           | [MEM_INSTANCED_80][]  | N/A         |
RTL           | [FUNC_IMPLEMENTED][]  | Done        |
RTL           | [ASSERT_KNOWN_ADDED][]| Done        |
Code Quality  | [LINT_SETUP][]        | Done        |
Review        | Reviewer(s)           | Done        | @sjgitty @shakushw
Review        | Signoff date          | Done        | 2019-10-29

[RV_TIMER Spec]:      {{<relref "/hw/ip/rv_timer/doc/_index.md">}}

[SPEC_COMPLETE]:      {{<relref "/doc/project/checklist.md#spec-complete" >}}
[CSR_DEFINED]:        {{<relref "/doc/project/checklist.md#csr-defined" >}}
[CLKRST_CONNECTED]:   {{<relref "/doc/project/checklist.md#clkrst-connected" >}}
[IP_TOP]:             {{<relref "/doc/project/checklist.md#ip-top" >}}
[IP_INSTANTIABLE]:    {{<relref "/doc/project/checklist.md#ip-instantiable" >}}
[MEM_INSTANCED_80]:   {{<relref "/doc/project/checklist.md#mem-instanced-80" >}}
[FUNC_IMPLEMENTED]:   {{<relref "/doc/project/checklist.md#func-implemented" >}}
[ASSERT_KNOWN_ADDED]: {{<relref "/doc/project/checklist.md#assert-known-added" >}}
[LINT_SETUP]:         {{<relref "/doc/project/checklist.md#lint-setup" >}}
[D1_REVIEWED]:        {{<relref "/doc/project/checklist.md#d1-reviewed" >}}

### D2

Type          | Item                    | Resolution     | Note/Collaterals
--------------|-------------------------|----------------|------------------
Documentation | [NEW_FEATURES][]        | N/A            |
Documentation | [BLOCK_DIAGRAM][]       | Done           |
Documentation | [DOC_INTERFACE][]       | Done           |
Documentation | [MISSING_FUNC][]        | N/A            |
Documentation | [FEATURE_FROZEN][]      | Done           |
RTL           | [FEATURE_COMPLETE][]    | Done           |
RTL           | [AREA_SANITY_CHECK][]   | Done           |
RTL           | [PORT_FROZEN][]         | Done w/ waiver | Change intr port name
RTL           | [ARCHITECTURE_FROZEN][] | Done           |
RTL           | [REVIEW_TODO][]         | Done           | [#68][]
RTL           | [STYLE_X][]             | Done           |
Code Quality  | [LINT_PASS][]           | Done           |
Code Quality  | [CDC_SETUP][]           | N/A            |
Code Quality  | [FPGA_TIMING][]         | Done           |
Code Quality  | [CDC_SYNCMACRO][]       | N/A            |
Review        | Reviewer(s)             | Done           | @sjgitty @shakushw
Review        | Signoff date            | Done           | 2019-10-29

[#68]: https://github.com/lowRISC/opentitan/issues/68

[NEW_FEATURES]:        {{<relref "/doc/project/checklist.md#new-features" >}}
[BLOCK_DIAGRAM]:       {{<relref "/doc/project/checklist.md#block-diagram" >}}
[DOC_INTERFACE]:       {{<relref "/doc/project/checklist.md#doc-interface" >}}
[MISSING_FUNC]:        {{<relref "/doc/project/checklist.md#missing-func" >}}
[FEATURE_FROZEN]:      {{<relref "/doc/project/checklist.md#feature-frozen" >}}
[FEATURE_COMPLETE]:    {{<relref "/doc/project/checklist.md#feature-complete" >}}
[AREA_SANITY_CHECK]:   {{<relref "/doc/project/checklist.md#area-sanity-check" >}}
[PORT_FROZEN]:         {{<relref "/doc/project/checklist.md#port-frozen" >}}
[ARCHITECTURE_FROZEN]: {{<relref "/doc/project/checklist.md#architecture-frozen" >}}
[REVIEW_TODO]:         {{<relref "/doc/project/checklist.md#review-todo" >}}
[STYLE_X]:             {{<relref "/doc/project/checklist.md#style-x" >}}
[LINT_PASS]:           {{<relref "/doc/project/checklist.md#lint-pass" >}}
[CDC_SETUP]:           {{<relref "/doc/project/checklist.md#cdc-setup" >}}
[CDC_SYNCMACRO]:       {{<relref "/doc/project/checklist.md#cdc-syncmacro" >}}
[FPGA_TIMING]:         {{<relref "/doc/project/checklist.md#fpga-timing" >}}
[D2_REVIEWED]:         {{<relref "/doc/project/checklist.md#d2-reviewed" >}}

### D3

 Type         | Item                    | Resolution  | Note/Collaterals
--------------|-------------------------|-------------|------------------
Documentation | [NEW_FEATURES_D3][]     | N/A         |
RTL           | [TODO_COMPLETE][]       | Done        |
Code Quality  | [LINT_COMPLETE][]       | Done        |
Code Quality  | [CDC_COMPLETE][]        | N/A         |
Review        | [REVIEW_RTL][]          | Done        | by @tjaychen
Review        | [REVIEW_DELETED_FF][]   | N/A         | on FPGA
Review        | [REVIEW_SW_CSR][]       | Done        |
Review        | [REVIEW_SW_FATAL_ERR][] | Done        | by @moidx
Review        | [REVIEW_SW_CHANGE][]    | N/A         |
Review        | [REVIEW_SW_ERRATA][]    | N/A         |
Review        | Reviewer(s)             | Done        | @tjaychen @sjgitty @shakushw
Review        | Signoff date            | Done        | 2019-10-30

[NEW_FEATURES_D3]:      {{<relref "/doc/project/checklist.md#new-features-d3" >}}
[TODO_COMPLETE]:        {{<relref "/doc/project/checklist.md#todo-complete" >}}
[LINT_COMPLETE]:        {{<relref "/doc/project/checklist.md#lint-complete" >}}
[CDC_COMPLETE]:         {{<relref "/doc/project/checklist.md#cdc-complete" >}}
[REVIEW_RTL]:           {{<relref "/doc/project/checklist.md#review-rtl" >}}
[REVIEW_DBG]:           {{<relref "/doc/project/checklist.md#review-dbg" >}}
[REVIEW_DELETED_FF]:    {{<relref "/doc/project/checklist.md#review-deleted-ff" >}}
[REVIEW_SW_CSR]:        {{<relref "/doc/project/checklist.md#review-sw-csr" >}}
[REVIEW_SW_FATAL_ERR]:  {{<relref "/doc/project/checklist.md#review-sw-fatal-err" >}}
[REVIEW_SW_CHANGE]:     {{<relref "/doc/project/checklist.md#review-sw-change" >}}
[REVIEW_SW_ERRATA]:     {{<relref "/doc/project/checklist.md#review-sw-errata" >}}
[D3_REVIEWED]:          {{<relref "/doc/project/checklist.md#d3-reviewed" >}}

## Verification Checklist

### V1

 Type         | Item                                  | Resolution      | Note/Collaterals
--------------|---------------------------------------|-----------------|------------------
Documentation | [DV_PLAN_DRAFT_COMPLETED][]           | Done            | [rv_timer_dv_plan]({{<relref "dv_plan/index.md" >}})
Documentation | [TESTPLAN_COMPLETED][]                | Done            |
Testbench     | [TB_TOP_CREATED][]                    | Done            |
Testbench     | [PRELIMINARY_ASSERTION_CHECKS_ADDED][]| Done            |
Testbench     | [SIM_TB_ENV_CREATED][]                | Done            |
Testbench     | [SIM_RAL_MODEL_GEN_AUTOMATED][]       | Done            |
Testbench     | [CSR_CHECK_GEN_AUTOMATED][]           | waived          | Revisit later. Tool setup in progress.
Testbench     | [TB_GEN_AUTOMATED][]                  | N/A             |
Tests         | [SIM_SANITY_TEST_PASSING][]           | Done            |
Tests         | [SIM_CSR_MEM_TEST_SUITE_PASSING][]    | Done            |
Tests         | [FPV_MAIN_ASSERTIONS_PROVEN][]        | N/A             |
Tool Setup    | [SIM_ALT_TOOL_SETUP][]                | Done            |
Regression    | [SIM_SANITY_REGRESSION_SETUP][]       | Done w/ waivers | Exception (implemented in local)
Regression    | [SIM_NIGHTLY_REGRESSION_SETUP][]      | Done w/ waivers | Exception (implemented in local)
Regression    | [FPV_REGRESSION_SETUP][]              | N/A             |
Coverage      | [SIM_COVERAGE_MODEL_ADDED][]          | Done            |
Integration   | [PRE_VERIFIED_SUB_MODULES_V1][]       | N/A             |
Review        | [DESIGN_SPEC_REVIEWED][]              | Done            |
Review        | [DV_PLAN_TESTPLAN_REVIEWED][]         | Done            |
Review        | [STD_TEST_CATEGORIES_PLANNED][]       | Done            | Exception (Security, Power, Debug)
Review        | [V2_CHECKLIST_SCOPED][]               | Done            |
Review        | Reviewer(s)                           | Done            | @eunchan @sjgitty @sriyerg
Review        | Signoff date                          | Done            | 2019-10-29


[DV_PLAN_DRAFT_COMPLETED]:            {{<relref "/doc/project/checklist.md#dv-plan-draft-completed" >}}
[TESTPLAN_COMPLETED]:                 {{<relref "/doc/project/checklist.md#testplan-completed" >}}
[TB_TOP_CREATED]:                     {{<relref "/doc/project/checklist.md#tb-top-created" >}}
[PRELIMINARY_ASSERTION_CHECKS_ADDED]: {{<relref "/doc/project/checklist.md#preliminary-assertion-checks-added" >}}
[SIM_TB_ENV_CREATED]:                 {{<relref "/doc/project/checklist.md#sim-tb-env-created" >}}
[SIM_RAL_MODEL_GEN_AUTOMATED]:        {{<relref "/doc/project/checklist.md#sim-ral-model-gen-automated" >}}
[CSR_CHECK_GEN_AUTOMATED]:            {{<relref "/doc/project/checklist.md#csr-check-gen-automated" >}}
[TB_GEN_AUTOMATED]:                   {{<relref "/doc/project/checklist.md#tb-gen-automated" >}}
[SIM_SANITY_TEST_PASSING]:            {{<relref "/doc/project/checklist.md#sanity-test-passing" >}}
[SIM_CSR_MEM_TEST_SUITE_PASSING]:     {{<relref "/doc/project/checklist.md#csr-mem-test-suite-passing" >}}
[FPV_MAIN_ASSERTIONS_PROVEN]:         {{<relref "/doc/project/checklist.md#fpv-main-assertions-proven" >}}
[SIM_ALT_TOOL_SETUP]:                 {{<relref "/doc/project/checklist.md#sim-alt-tool-setup" >}}
[SIM_SANITY_REGRESSION_SETUP]:        {{<relref "/doc/project/checklist.md#sim-sanity-regression-setup" >}}
[SIM_NIGHTLY_REGRESSION_SETUP]:       {{<relref "/doc/project/checklist.md#sim-nightly-regression-setup" >}}
[FPV_REGRESSION_SETUP]:               {{<relref "/doc/project/checklist.md#fpv-regression-setup" >}}
[SIM_COVERAGE_MODEL_ADDED]:           {{<relref "/doc/project/checklist.md#sim-coverage-model-added" >}}
[PRE_VERIFIED_SUB_MODULES_V1]:        {{<relref "/doc/project/checklist.md#pre-verified-sub-modules-v1" >}}
[DESIGN_SPEC_REVIEWED]:               {{<relref "/doc/project/checklist.md#design-spec-reviewed" >}}
[DV_PLAN_TESTPLAN_REVIEWED]:          {{<relref "/doc/project/checklist.md#dv-plan-testplan-reviewed" >}}
[STD_TEST_CATEGORIES_PLANNED]:        {{<relref "/doc/project/checklist.md#std-test-categories-planned" >}}
[V2_CHECKLIST_SCOPED]:                {{<relref "/doc/project/checklist.md#v2-checklist-scoped" >}}

### V2

 Type         | Item                                    | Resolution  | Note/Collaterals
--------------|-----------------------------------------|-------------|------------------
Documentation | [DESIGN_DELTAS_CAPTURED_V2][]           | N/A         |
Documentation | [DV_PLAN_COMPLETED][]                   | Done        |
Testbench     | [ALL_INTERFACES_EXERCISED][]            | Done        |
Testbench     | [ALL_ASSERTION_CHECKS_ADDED][]          | Done        |
Testbench     | [SIM_TB_ENV_COMPLETED][]                | Done        |
Tests         | [SIM_ALL_TESTS_PASSING][]               | Done        |
Tests         | [FPV_ALL_ASSERTIONS_WRITTEN][]          | N/A         |
Tests         | [FPV_ALL_ASSUMPTIONS_REVIEWED][]        | N/A         |
Tests         | [SIM_FW_SIMULATED][]                    | N/A         |
Regression    | [SIM_NIGHTLY_REGRESSION_V2][]           | Done        |
Coverage      | [SIM_CODE_COVERAGE_V2][]                | Done        |
Coverage      | [SIM_FUNCTIONAL_COVERAGE_V2][]          | Done        |
Coverage      | [FPV_CODE_COVERAGE_V2][]                | N/A         |
Coverage      | [FPV_COI_COVERAGE_V2][]                 | N/A         |
Issues        | [NO_HIGH_PRIORITY_ISSUES_PENDING][]     | Done        |
Issues        | [ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED][] | Done        | [#68][], [#69][]
Integration   | [PRE_VERIFIED_SUB_MODULES_V2][]         | N/A         |
Review        | [V3_CHECKLIST_SCOPED][]                 | Done        |
Review        | Reviewer(s)                             | Done        | @eunchan @sjgitty @sriyerg
Review        | Signoff date                            | Done        | 2019-11-01

[#69]: https://github.com/lowRISC/opentitan/issues/69

[DESIGN_DELTAS_CAPTURED_V2]:          {{<relref "/doc/project/checklist.md#design-deltas-captured-v2" >}}
[DV_PLAN_COMPLETED]:                  {{<relref "/doc/project/checklist.md#dv-plan-completed" >}}
[ALL_INTERFACES_EXERCISED]:           {{<relref "/doc/project/checklist.md#all-interfaces-exercised" >}}
[ALL_ASSERTION_CHECKS_ADDED]:         {{<relref "/doc/project/checklist.md#all-assertion-checks-added" >}}
[SIM_TB_ENV_COMPLETED]:               {{<relref "/doc/project/checklist.md#sim-tb-env-completed" >}}
[SIM_ALL_TESTS_PASSING]:              {{<relref "/doc/project/checklist.md#sim-all-tests-passing" >}}
[FPV_ALL_ASSERTIONS_WRITTEN]:         {{<relref "/doc/project/checklist.md#fpv-all-assertions-written" >}}
[FPV_ALL_ASSUMPTIONS_REVIEWED]:       {{<relref "/doc/project/checklist.md#fpv-all-assumptions-reviewed" >}}
[SIM_FW_SIMULATED]:                   {{<relref "/doc/project/checklist.md#sim-fw-simulated" >}}
[SIM_NIGHTLY_REGRESSION_V2]:          {{<relref "/doc/project/checklist.md#sim-nightly-regression-v2" >}}
[SIM_CODE_COVERAGE_V2]:               {{<relref "/doc/project/checklist.md#sim-code-coverage-v2" >}}
[SIM_FUNCTIONAL_COVERAGE_V2]:         {{<relref "/doc/project/checklist.md#sim-functional-coverage-v2" >}}
[FPV_CODE_COVERAGE_V2]:               {{<relref "/doc/project/checklist.md#fpv-code-coverage-v2" >}}
[FPV_COI_COVERAGE_V2]:                {{<relref "/doc/project/checklist.md#fpv-coi-coverage-v2" >}}
[NO_HIGH_PRIORITY_ISSUES_PENDING]:    {{<relref "/doc/project/checklist.md#no-high-priority-issues-pending" >}}
[ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED]:{{<relref "/doc/project/checklist.md#all-low-priority-issues-root-caused" >}}
[PRE_VERIFIED_SUB_MODULES_V2]:        {{<relref "/doc/project/checklist.md#pre-verified-sub-modules-v2" >}}
[V3_CHECKLIST_SCOPED]:                {{<relref "/doc/project/checklist.md#v3-checklist-scoped" >}}

### V3

 Type         | Item                              | Resolution  | Note/Collaterals
--------------|-----------------------------------|-------------|------------------
Documentation | [DESIGN_DELTAS_CAPTURED_V3][]     | N/A         |
Testbench     | [ALL_TODOS_RESOLVED][]            | Done        | Resolved: [#671][]
Tests         | [X_PROP_ANALYSIS_COMPLETED][]     | Waived      | Revisit later. Tool setup in progress.
Tests         | [FPV_ASSERTIONS_PROVEN_AT_V3][]   | N/A         |
Regression    | [SIM_NIGHTLY_REGRESSION_AT_V3][]  | Done        | Exception (implemented in local)
Coverage      | [SIM_CODE_COVERAGE_AT_100][]      | Done        | Merge common exclusions then add rv_timer specifics.
Coverage      | [SIM_FUNCTIONAL_COVERAGE_AT_100][]| Done        | Resolved: [sticky reset][#844]
Coverage      | [FPV_CODE_COVERAGE_AT_100][]      | N/A         |
Coverage      | [FPV_COI_COVERAGE_AT_100][]       | N/A         |
Issues        | [NO_ISSUES_PENDING][]             | Done        | [#68][], [#69][]
Code Quality  | [NO_TOOL_WARNINGS_THROWN][]       | Done        |
Integration   | [PRE_VERIFIED_SUB_MODULES_V3][]   | N/A         |
Review        | Reviewer(s)                       | Done        | @eunchan @sjgitty @sriyerg
Review        | Signoff date                      | Done        | 2019-11-04

[#671]: https://github.com/lowRISC/opentitan/pull/671
[#844]: https://github.com/lowRISC/opentitan/pull/844

[DESIGN_DELTAS_CAPTURED_V3]:     {{<relref "/doc/project/checklist.md#design-deltas-captured-v3" >}}
[ALL_TODOS_RESOLVED]:            {{<relref "/doc/project/checklist.md#all-todos-resolved" >}}
[X_PROP_ANALYSIS_COMPLETED]:     {{<relref "/doc/project/checklist.md#x-prop-analysis-completed" >}}
[FPV_ASSERTIONS_PROVEN_AT_V3]:   {{<relref "/doc/project/checklist.md#fpv-assertions-proven-at-v3" >}}
[SIM_NIGHTLY_REGRESSION_AT_V3]:  {{<relref "/doc/project/checklist.md#sim-nightly-regression-at-v3" >}}
[SIM_CODE_COVERAGE_AT_100]:      {{<relref "/doc/project/checklist.md#sim-code-coverage-at-100" >}}
[SIM_FUNCTIONAL_COVERAGE_AT_100]:{{<relref "/doc/project/checklist.md#sim-functional-coverage-at-100" >}}
[FPV_CODE_COVERAGE_AT_100]:      {{<relref "/doc/project/checklist.md#fpv-code-coverage-at-100" >}}
[FPV_COI_COVERAGE_AT_100]:       {{<relref "/doc/project/checklist.md#fpv-coi-coverage-at-100" >}}
[NO_ISSUES_PENDING]:             {{<relref "/doc/project/checklist.md#no-issues-pending" >}}
[NO_TOOL_WARNINGS_THROWN]:       {{<relref "/doc/project/checklist.md#no-tool-warnings-thrown" >}}
[PRE_VERIFIED_SUB_MODULES_V3]:   {{<relref "/doc/project/checklist.md#pre-verified-sub-modules-v3" >}}

