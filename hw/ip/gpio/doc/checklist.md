---
title: "GPIO Checklist"
---

This checklist is for [Hardware Stage]({{<relref "/doc/project/hw_stages.md">}}) transitions for the [GPIO peripheral][GPIO Spec].
All checklist items refer to the content in the [Checklist.]({{<relref "/doc/project/checklist.md">}})

## Design Checklist

### D1

Type          | Item                  | Resolution  | Note/Collaterals
--------------|-----------------------|-------------|------------------
Documentation | [SPEC_COMPLETE][]     | Done        | [GPIO Spec][]
Documentation | [CSR_DEFINED][]       | Done        | [GPIO CSR][]
RTL           | [CLKRST_CONNECTED][]  | Done        |
RTL           | [IP_TOP][]            | Done        |
RTL           | [IP_INSTANTIABLE][]      | Done        |
RTL           | [MEM_INSTANCED_80][]  | N/A         |
RTL           | [FUNC_IMPLEMENTED][]  | Done        |
RTL           | [ASSERT_KNOWN_ADDED][]| Done        |
Code Quality  | [LINT_SETUP][]        | Done        |
Review        | Reviewer(s)           | Done        | @sjgitty @gaurangchitroda
Review        | Signoff date          | Done        | 2019-10-30

[GPIO Spec]: ../
[GPIO CSR]: ../data/gpio.hjson


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

Type          | Item                    | Resolution  | Note/Collaterals
--------------|-------------------------|-------------|------------------
Documentation | [NEW_FEATURES][]        | N/A         |
Documentation | [BLOCK_DIAGRAM][]       | N/A         |
Documentation | [DOC_INTERFACE][]       | Done        |
Documentation | [MISSING_FUNC][]        | N/A         |
Documentation | [FEATURE_FROZEN][]      | Done        |
RTL           | [FEATURE_COMPLETE][]    | Done        |
RTL           | [AREA_SANITY_CHECK][]   | Done        |
RTL           | [PORT_FROZEN][]         | Done        |
RTL           | [ARCHITECTURE_FROZEN][] | Done        |
RTL           | [REVIEW_TODO][]         | Done        |
RTL           | [STYLE_X][]             | N/A         | No assignment of X
Code Quality  | [LINT_PASS][]           | Done        | Lint waivers reviewed
Code Quality  | [CDC_SETUP][]           | N/A         | No CDC path
Code Quality  | [FPGA_TIMING][]         | Done        | Fmax 50MHz on NexysVideo
Code Quality  | [CDC_SYNCMACRO][]       | N/A         |
Review        | Reviewer(s)             | Done        | @sjgitty @gaurangchitroda @aytong
Review        | Signoff date            | Done        | 2019-10-30

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
RTL           | [TODO_COMPLETE][]       | Done        | No TODO
Code Quality  | [LINT_COMPLETE][]       | Done        |
Code Quality  | [CDC_COMPLETE][]        | N/A         |
Review        | [REVIEW_RTL][]          | Done        | Reviewed by @msfschaffner
Review        | [REVIEW_DELETED_FF][]   | N/A         | Not reported by FPGA tool
Review        | [REVIEW_SW_CSR][]       | Done        |
Review        | [REVIEW_SW_FATAL_ERR][] | Done        |
Review        | [REVIEW_SW_CHANGE][]    | Done        |
Review        | [REVIEW_SW_ERRATA][]    | Done        |
Review        | Reviewer(s)             | Done        | @gkelly @sjgitty @gaurangchitroda
Review        | Signoff date            | Done        | 2019-11-04

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
Documentation | [DV_PLAN_DRAFT_COMPLETED][]           | Done            | [gpio_dv_plan][{{<relref "dv_plan/" >}}]
Documentation | [TESTPLAN_COMPLETED][]                | Done            |
Testbench     | [TB_TOP_CREATED][]                    | Done            |
Testbench     | [PRELIMINARY_ASSERTION_CHECKS_ADDED][]| Done            |
Testbench     | [TB_ENV_CREATED][]                    | Done            |
Testbench     | [RAL_MODEL_GEN_AUTOMATED][]           | Done            |
Testbench     | [TB_GEN_AUTOMATED][]                  | N/A             |
Tests         | [SANITY_TEST_PASSING][]               | Done            |
Tests         | [CSR_MEM_TEST_SUITE_PASSING][]        | Done            |
Tool Setup    | [ALT_TOOL_SETUP][]                    | Done            |
Regression    | [SANITY_REGRESSION_SETUP][]           | Done w/ waivers | Exception (implemented in local)
Regression    | [NIGHTLY_REGRESSION_SETUP][]          | Done w/ waivers | Exception (implemented in local)
Coverage      | [COVERAGE_MODEL_ADDED][]              | Done            |
Integration   | [PRE_VERIFIED_SUB_MODULES_V1][]       | N/A             |
Review        | [DESIGN_SPEC_REVIEWED][]              | Done            |
Review        | [DV_PLAN_TESTPLAN_REVIEWED][]         | Done            |
Review        | [STD_TEST_CATEGORIES_PLANNED][]       | Done            | Exception (Security, Power, Debug)
Review        | [V2_CHECKLIST_SCOPED][]               | Done            |
Review        | Reviewer(s)                           | Done            | @eunchan @sjgitty @sriyerg
Review        | Signoff date                          | Done            | 2019-10-30

[gpio_dv_plan]: {{<relref "/hw/ip/gpio/doc/dv_plan/index.md">}}

[DV_PLAN_DRAFT_COMPLETED]:            {{<relref "/doc/project/checklist.md#dv-plan-draft-completed" >}}
[TESTPLAN_COMPLETED]:                 {{<relref "/doc/project/checklist.md#testplan-completed" >}}
[TB_TOP_CREATED]:                     {{<relref "/doc/project/checklist.md#tb-top-created" >}}
[PRELIMINARY_ASSERTION_CHECKS_ADDED]: {{<relref "/doc/project/checklist.md#preliminary-assertion-checks-added" >}}
[TB_ENV_CREATED]:                     {{<relref "/doc/project/checklist.md#tb-env-created" >}}
[RAL_MODEL_GEN_AUTOMATED]:            {{<relref "/doc/project/checklist.md#ral-model-gen-automated" >}}
[TB_GEN_AUTOMATED]:                   {{<relref "/doc/project/checklist.md#tb-gen-automated" >}}
[SANITY_TEST_PASSING]:                {{<relref "/doc/project/checklist.md#sanity-test-passing" >}}
[CSR_MEM_TEST_SUITE_PASSING]:         {{<relref "/doc/project/checklist.md#csr-mem-test-suite-passing" >}}
[ALT_TOOL_SETUP]:                     {{<relref "/doc/project/checklist.md#alt-tool-setup" >}}
[SANITY_REGRESSION_SETUP]:            {{<relref "/doc/project/checklist.md#sanity-regression-setup" >}}
[NIGHTLY_REGRESSION_SETUP]:           {{<relref "/doc/project/checklist.md#nightly-regression-setup" >}}
[COVERAGE_MODEL_ADDED]:               {{<relref "/doc/project/checklist.md#coverage-model-added" >}}
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
Testbench     | [TB_ENV_COMPLETED][]                    | Done        |
Tests         | [ALL_TESTS_PASSING][]                   | Done        | Resolved: [#680][]
Tests         | [FW_SIMULATED][]                        | N/A         |
Regression    | [NIGHTLY_REGRESSION_V2][]               | Done        |
Coverage      | [CODE_COVERAGE_V2][]                    | Done        |
Coverage      | [FUNCTIONAL_COVERAGE_V2][]              | Done        | Resolved: [#807][]
Issues        | [NO_HIGH_PRIORITY_ISSUES_PENDING][]     | Done        |
Issues        | [ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED][] | Done        | [#41][] Not quite related, [#45][] root caused
Integration   | [PRE_VERIFIED_SUB_MODULES_V2][]         | N/A         |
Review        | [V3_CHECKLIST_SCOPED][]                 | Done        |
Review        | Reviewer(s)                             | Done        | @sjgitty @eunchan @sriyerg
Review        | Signoff date                            | Done        | 2019-11-04

[#41]: https://github.com/lowRISC/opentitan/issues/41
[#45]: https://github.com/lowRISC/opentitan/issues/45
[#680]: https://github.com/lowRISC/opentitan/pull/680
[#807]: https://github.com/lowRISC/opentitan/pull/807

[DESIGN_DELTAS_CAPTURED_V2]:          {{<relref "/doc/project/checklist.md#design-deltas-captured-v2" >}}
[DV_PLAN_COMPLETED]:                  {{<relref "/doc/project/checklist.md#dv-plan-completed" >}}
[ALL_INTERFACES_EXERCISED]:           {{<relref "/doc/project/checklist.md#all-interfaces-exercised" >}}
[ALL_ASSERTION_CHECKS_ADDED]:         {{<relref "/doc/project/checklist.md#all-assertion-checks-added" >}}
[TB_ENV_COMPLETED]:                   {{<relref "/doc/project/checklist.md#tb-env-completed" >}}
[ALL_TESTS_PASSING]:                  {{<relref "/doc/project/checklist.md#all-tests-passing" >}}
[FW_SIMULATED]:                       {{<relref "/doc/project/checklist.md#fw-simulated" >}}
[NIGHTLY_REGRESSION_V2]:              {{<relref "/doc/project/checklist.md#nightly-regression-v2" >}}
[CODE_COVERAGE_V2]:                   {{<relref "/doc/project/checklist.md#code-coverage-v2" >}}
[FUNCTIONAL_COVERAGE_V2]:             {{<relref "/doc/project/checklist.md#functional-coverage-v2" >}}
[NO_HIGH_PRIORITY_ISSUES_PENDING]:    {{<relref "/doc/project/checklist.md#no-high-priority-issues-pending" >}}
[ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED]:{{<relref "/doc/project/checklist.md#all-low-priority-issues-root-caused" >}}
[PRE_VERIFIED_SUB_MODULES_V2]:        {{<relref "/doc/project/checklist.md#pre-verified-sub-modules-v2" >}}
[V3_CHECKLIST_SCOPED]:                {{<relref "/doc/project/checklist.md#v3-checklist-scoped" >}}

### V3

 Type         | Item                              | Resolution  | Note/Collaterals
--------------|-----------------------------------|-------------|------------------
Documentation | [DESIGN_DELTAS_CAPTURED_V3][]     | N/A         |
Testbench     | [ALL_TODOS_RESOLVED][]            | Done        |
Tests         | [X_PROP_ANALYSIS_COMPLETED][]     | Waived      | Revisit later. Tool setup in progress.
Regression    | [NIGHTLY_REGRESSION_AT_100][]     | Done        | Resolved: [#680][]
Coverage      | [CODE_COVERAGE_AT_100][]          | Done        | [common_cov_excl.el][], [gpio_cov_excl.el][]
Coverage      | [FUNCTIONAL_COVERAGE_AT_100][]    | Done        | [#807][]
Issues        | [NO_ISSUES_PENDING][]             | Done        |
Code Quality  | [NO_TOOL_WARNINGS_THROWN][]       | Done        |
Integration   | [PRE_VERIFIED_SUB_MODULES_V3][]   | N/A         |
Review        | Reviewer(s)                       | Done        | @eunchan @sriyerg @sjgitty
Review        | Signoff date                      | Done        | 2019-11-04

[#807]: https://github.com/lowRISC/opentitan/pull/807

[DESIGN_DELTAS_CAPTURED_V3]:    {{<relref "/doc/project/checklist.md#design-deltas-captured-v3" >}}
[ALL_TODOS_RESOLVED]:           {{<relref "/doc/project/checklist.md#all-todos-resolved" >}}
[X_PROP_ANALYSIS_COMPLETED]:    {{<relref "/doc/project/checklist.md#x-prop-analysis-completed" >}}
[NIGHTLY_REGRESSION_AT_100]:    {{<relref "/doc/project/checklist.md#nightly-regression-at-100" >}}
[CODE_COVERAGE_AT_100]:         {{<relref "/doc/project/checklist.md#code-coverage-at-100" >}}
[FUNCTIONAL_COVERAGE_AT_100]:   {{<relref "/doc/project/checklist.md#functional-coverage-at-100" >}}
[NO_ISSUES_PENDING]:            {{<relref "/doc/project/checklist.md#no-issues-pending" >}}
[NO_TOOL_WARNINGS_THROWN]:      {{<relref "/doc/project/checklist.md#no-tool-warnings-thrown" >}}
[PRE_VERIFIED_SUB_MODULES_V3]:  {{<relref "/doc/project/checklist.md#pre-verified-sub-modules-v3" >}}

[common_cov_excl.el]:https://github.com/lowRISC/opentitan/blob/9dff09b6c57f4962d67f5f64f8e69ac9bea6885c/hw/dv/tools/vcs/common_cov_excl.el
[gpio_cov_excl.el]:  https://github.com/lowRISC/opentitan/blob/39aaeefdb43661b065c29ceab2efc1065aebf6dd/hw/ip/gpio/dv/cov/gpio_cov_excl.el
