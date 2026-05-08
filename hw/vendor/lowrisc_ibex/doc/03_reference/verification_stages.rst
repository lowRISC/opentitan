.. _verification_stages:

Verification Stages
===================

Ibex is being verified as part of the `OpenTitan <https://www.opentitan.org>`_ project and follows the `verification stages used in OpenTitan <https://opentitan.org/book/doc/project_governance/development_stages.html#hardware-verification-stages-v>`_.
The current verification stage of the 'opentitan' configuration of Ibex is **V2S**.
The full definition of V2S can be found at the `OpenTitan V2 <https://opentitan.org/book/doc/project_governance/checklist/index.html#v2>`_ and `OpenTitan V2S <https://opentitan.org/book/doc/project_governance/checklist/index.html#v2s>`_ checklists.
Other Ibex configurations do not have a formal verification stage at present.

V1 Checklist
------------

+---------------+------------------------------------+------------+-------------------------------------------------------+
| Type          | Item                               | Resolution | Notes                                                 |
+===============+====================================+============+=======================================================+
| Documentation | DV_DOC_DRAFT_COMPLETE              | Waived     | Plan created, but does not conform to other templates |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Documentation | TESTPLAN_COMPLETED                 | Done       |                                                       |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Testbench     | TB_TOP_CREATED                     | Done       |                                                       |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Testbench     | PRELIMINARY_ASSERTION_CHECKS_ADDED | N/A        |                                                       |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Testbench     | SIM_TB_ENV_CREATED                 | Done       |                                                       |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Testbench     | SIM_RAL_MODEL_GEN_AUTOMATED        | N/A        |                                                       |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Testbench     | CSR_CHECK_GEN_AUTOMATED            | N/A        |                                                       |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Testbench     | TB_GEN_AUTOMATED                   | N/A        |                                                       |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Tests         | SIM_SMOKE_TEST_PASSING             | Done       |                                                       |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Tests         | SIM_CSR_MEM_TEST_SUITE_PASSING     | Done       |                                                       |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Tests         | FPV_MAIN_ASSERTIONS_PROVEN         | N/A        |                                                       |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Tool Setup    | SIM_ALT_TOOL_SETUP                 | Waived     | waived for now, doesn’t follow standard tool flow     |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Regression    | SIM_SMOKE_REGRESSION_SETUP         | Done       |                                                       |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Regression    | SIM_NIGHTLY_REGRESSION_SETUP       | Done       |                                                       |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Regression    | FPV_REGRESSION_SETUP               | N/A        |                                                       |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Coverage      | SIM_COVERAGE_MODEL_ADDED           | Done       |                                                       |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Code Quality  | TB_LINT_SETUP                      | Waived     |                                                       |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Integration   | PRE_VERIFIED_SUB_MODULES_V1        | N/A        |                                                       |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Review        | DESIGN_SPEC_REVIEWED               | Done       |                                                       |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Review        | TESTPLAN_REVIEWED                  | Waived     | Not done, will be reviewed in V2                      |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Review        | STD_TEST_CATEGORIES_PLANNED        | Done       | different format than comportable modules             |
+---------------+------------------------------------+------------+-------------------------------------------------------+
| Review        | V2_CHECKLIST_SCOPED                | Done       |                                                       |
+---------------+------------------------------------+------------+-------------------------------------------------------+

V2 Checklist
------------

+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Type          | Item                                | Resolution | Notes                                                                                                                                                                |
+===============+=====================================+============+======================================================================================================================================================================+
| Documentation | DESIGN_DELTAS_CAPTURED_V2           | Complete   |                                                                                                                                                                      |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Testbench     | FUNCTIONAL_COVERAGE_IMPLEMENTED     | Complete   |                                                                                                                                                                      |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Testbench     | ALL_INTERFACES_EXERCISED            | Complete   |                                                                                                                                                                      |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Testbench     | ALL_ASSERTION_CHECKS_ADDED          | Complete   |                                                                                                                                                                      |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Testbench     | SIM_TB_ENV_COMPLETED                | Complete   |                                                                                                                                                                      |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Tests         | SIM_ALL_TESTS_PASSING               | Complete   | Note the ``riscv_assorted_traps_interrupts_debug`` test sees many failures (but does have some seeds that pass).                                                     |
|               |                                     |            | The test attempts to generally combine many different stimuli and under OpenTitan classification would be considered a V3 test.                                      |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Tests         | FPV_ALL_ASSERTIONS_WRITTEN          | N/A        | No formal applied for non-security features in Ibex.                                                                                                                 |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Tests         | FPV_ALL_ASSUMPTIONS_REVIEWED        | N/A        | No formal applied for non-security features in Ibex.                                                                                                                 |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Tests         | SIM_FW_SIMULATED                    | N/A        | No ROM or firmware present.                                                                                                                                          |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Regression    | SIM_NIGHTLY_REGRESSION_V2           | Complete   | Regression run in GitHub Actions only accessible to OpenTitan members.                                                                                               |
|               |                                     |            | Publicly viewable reports on the `OpenTitan regression dashboard <https://reports.opentitan.org/hw/top_earlgrey/dv/summary/latest/report.html>`_ are planned for V3. |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Coverage      | SIM_CODE_COVERAGE_V2                | Complete   | Coverage results available in nightly regression run.                                                                                                                |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Coverage      | SIM_FUNCTIONAL_COVERAGE_V2          | Complete   | Coverage results available in nightly regression run.                                                                                                                |
|               |                                     |            | Note the average grade (the average of coverage % for each individual coverpoint and cross) is used for the 90% figure.                                              |
|               |                                     |            | As the functional coverage contains some very large crosses a simple % of all bins hit biases too much toward these crosses.                                         |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Coverage      | FPV_CODE_COVERAGE_V2                | N/A        | No formal applied for non-security features in Ibex.                                                                                                                 |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Coverage      | FPV_COI_COVERAGE_V2                 | N/A        | No formal applied for non-security features in Ibex.                                                                                                                 |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Integration   | PRE_VERIFIED_SUB_MODULES_V2         | Complete   | ICache is verified in a separate testbench.                                                                                                                          |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Issues        | NO_HIGH_PRIORITY_ISSUES_PENDING     | Complete   |                                                                                                                                                                      |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Issues        | ALL_LOW_PRIORITY_ISSUES_ROOT_CAUSED | Complete   |                                                                                                                                                                      |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Review        | DV_DOC_TESTPLAN_REVIEWED            | Complete   |                                                                                                                                                                      |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Review        | V3_CHECKLIST_SCOPED                 | Complete   |                                                                                                                                                                      |
+---------------+-------------------------------------+------------+----------------------------------------------------------------------------------------------------------------------------------------------------------------------+

**PMP Testing Note**: A large number of iterations of ``pmp_full_random_test`` are required to meet coverage goals and timed out tests must be included in the coverage collection.
This is because of the large cross bins for PMP that aim to explore the full space of possible behaviour.
The current strategy of random generation is very inefficient at exploring this space.
It is also complex to write a randomly generated test that can deal with all possible scenarios without hitting a double faulting or time out scenarios (e.g. consider a random configuration that gives you no executable regions and ePMP modes like machine mode lockdown and machine mode whitelist policy).
Co-simulation checking is enabled when this test is run (as it is for all block level verification tests) so would detect any incorrect behaviour.
From investigation we are confident the time-outs seen are simply badly performing tests (e.g. very slowly working its way through an instruction block with no execute permissions by attempting to execute one instruction, faulting, trying the next and getting the same result over and over).
For future work we will explore more efficient strategies for exploring this space as well as employing formal methods to achieve full verification closure.

V2S Checklist
-------------

+---------------+--------------------------+------------+--------------------------------------------------------------------------------------------------------------------------------------+
| Type          | Item                     | Resolution | Notes                                                                                                                                |
+===============+==========================+============+======================================================================================================================================+
| Documentation | SEC_CM_TESTPLAN_COMPLETE | Complete   | The security counter measure to test mapping can be found below                                                                      |
+---------------+--------------------------+------------+--------------------------------------------------------------------------------------------------------------------------------------+
| Tests         | FPV_SEC_CM_VERIFIED      | Complete   | See the `OpenTitan FPV Results Dashboard <https://reports.opentitan.org/hw/top_earlgrey/formal/sec_cm/summary/latest/report.html>`_. |
+---------------+--------------------------+------------+--------------------------------------------------------------------------------------------------------------------------------------+
| Tests         | SIM_SEC_CM_VERIFIED      | Complete   |                                                                                                                                      |
+---------------+--------------------------+------------+--------------------------------------------------------------------------------------------------------------------------------------+
| Coverage      | SIM_COVERAGE_REVIEWED    | Complete   |                                                                                                                                      |
+---------------+--------------------------+------------+--------------------------------------------------------------------------------------------------------------------------------------+
| Review        | SEC_CM_DV_REVIEWED       | Complete   |                                                                                                                                      |
+---------------+--------------------------+------------+--------------------------------------------------------------------------------------------------------------------------------------+

Ibex SEC_CM Test Mapping
------------------------

The :ref:`security features Ibex implements <security>` are given specific security countermeasure names in OpenTitan (see 'Security Countermeasures' in the `Comportability Definition and Specification <https://opentitan.org/book/doc/contributing/hw/comportability/index.html#security-countermeasures>`_ documentation section).
Each countermeasure has a test that exercises it.
The mapping between countermeasures and tests is given below

+--------------------------------+------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| Security Countermeasure        | Test                                                                                                                                                                                                                                                                                                       |
+================================+============================================================================================================================================================================================================================================================================================================+
| BUS.INTEGRITY                  | ``riscv_mem_intg_error_test`` in Ibex DV.                                                                                                                                                                                                                                                                  |
|                                | The ``chip_sw_data_integrity`` OpenTitan top-level test will trigger integrity errors within the OpenTitan specific ``rv_core_ibex`` wrapper.                                                                                                                                                              |
|                                | The TL-UL host adapter used in the OpenTitan specific ``rv_core_ibex`` is fully verified elsewhere in OpenTitan.                                                                                                                                                                                           |
+--------------------------------+------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| SCRAMBLE.KEY.SIDELOAD          | ``riscv_rand_instr_test`` in Ibex DV.                                                                                                                                                                                                                                                                      |
|                                | This test executes ``FENCE.I`` which rotates the scramble key.                                                                                                                                                                                                                                             |
|                                | The ``rv_core_ibex_icache_invalidate_test`` OpenTitan top-level test covers assertions within the OpenTitan specific ``rv_core_ibex`` wrapper that check that a ``FENCE.I`` results in an icache scramble key request and that the returned key is correctly supplied to the scrambling memory primitives. |
+--------------------------------+------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| CORE.DATA_REG_SW.SCA           | ``dit_test`` directed test run against simple system cosimulation.                                                                                                                                                                                                                                         |
|                                | The test runs functions that whose timing is data dependent with data independent timing disabled.                                                                                                                                                                                                         |
|                                | It passes where the runs with data independent timing enabled all execute in the same amount of time and the runs without it enabled take different amounts of time.                                                                                                                                       |
+--------------------------------+------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| PC.CTRL_FLOW.CONSISTENCY       | ``riscv_pc_intg_test`` in Ibex DV.                                                                                                                                                                                                                                                                         |
+--------------------------------+------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| CTRL_FLOW.UNPREDICTABLE        | ``dummy_instr_test`` directed test run against simple system cosimulation.                                                                                                                                                                                                                                 |
|                                | The test runs a function with dummy instructions disabled and enabled.                                                                                                                                                                                                                                     |
|                                | It passes where the runs without dummy instructions all have the same timing and runs with dummy instructions all have different timing.                                                                                                                                                                   |
+--------------------------------+------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| DATA_REG_SW.INTEGRITY          | ``riscv_rf_intg_test`` in Ibex DV.                                                                                                                                                                                                                                                                         |
+--------------------------------+------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| DATA_REG_SW.GLITCH_DETECT      | Covered by formal verification of security countermeasures within OpenTitan.                                                                                                                                                                                                                               |
+--------------------------------+------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| LOGIC.SHADOW                   | ``chip_sw_rv_core_ibex_lockstep_glitch`` top-level test in OpenTitan                                                                                                                                                                                                                                       |
+--------------------------------+------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| FETCH.CTRL.LC_GATED            | ``riscv_rand_instr_test`` in Ibex DV.                                                                                                                                                                                                                                                                      |
|                                | Fetch enable is randomly toggled in various tests and correct behaviour checked via an assertion.                                                                                                                                                                                                          |
+--------------------------------+------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| EXCEPTION.CTRL_FLOW.LOCAL_ESC  | ``riscv_pmp_full_random_test`` in Ibex DV.                                                                                                                                                                                                                                                                 |
|                                | This test produces double faults, which are checked by an assertion.                                                                                                                                                                                                                                       |
|                                | ``chip_sw_rv_core_ibex_double_fault`` top-level test in OpenTitan demonstrates escalation on a double fault                                                                                                                                                                                                |
+--------------------------------+------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| EXCEPTION.CTRL_FLOW.GLOBAL_ESC | ``riscv_pmp_full_random_test`` in Ibex DV.                                                                                                                                                                                                                                                                 |
|                                | This test produces double faults, which are checked by an assertion.                                                                                                                                                                                                                                       |
|                                | ``chip_sw_rv_core_ibex_double_fault`` top-level test in OpenTitan demonstrates escalation on a double fault                                                                                                                                                                                                |
+--------------------------------+------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| ICACHE.MEM.SCRAMBLE            | No explicit testing, the scrambling memory primitive is separately verified within OpenTitan.                                                                                                                                                                                                              |
|                                | Assertions in the OpenTitan specific ``rv_core_ibex`` wrapper ensure a newly requested scramble key is correctly applied to the scrambling memories.                                                                                                                                                       |
|                                | The ``rv_core_ibex_icache_invalidate_test`` OpenTitan top-level test covers assertions within the OpenTitan specific ``rv_core_ibex`` wrapper that check that a ``FENCE.I`` results in an icache scramble key request and that the returned key is correctly supplied to the scrambling memory primitives. |
+--------------------------------+------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+
| ICACHE.MEM.INTEGRITY           | ``riscv_icache_intg_test`` in Ibex DV.                                                                                                                                                                                                                                                                     |
+--------------------------------+------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------+

V3 Checklist
------------

+---------------+--------------------------------+-------------+-------+
| Type          | Item                           | Resolution  | Notes |
+===============+================================+=============+=======+
| Documentation | DESIGN_DELTAS_CAPTURED_V3      | Not Started |       |
+---------------+--------------------------------+-------------+-------+
| Tests         | X_PROP_ANALYSIS_COMPLETED      | Not Started |       |
+---------------+--------------------------------+-------------+-------+
| Tests         | FPV_ASSERTIONS_PROVEN_AT_V3    | Not Started |       |
+---------------+--------------------------------+-------------+-------+
| Regression    | SIM_NIGHTLY_REGRESSION_AT_V3   | Not Started |       |
+---------------+--------------------------------+-------------+-------+
| Coverage      | SIM_CODE_COVERAGE_AT_100       | Not Started |       |
+---------------+--------------------------------+-------------+-------+
| Coverage      | SIM_FUNCTIONAL_COVERAGE_AT_100 | Not Started |       |
+---------------+--------------------------------+-------------+-------+
| Coverage      | FPV_CODE_COVERAGE_AT_100       | Not Started |       |
+---------------+--------------------------------+-------------+-------+
| Coverage      | FPV_COI_COVERAGE_AT_100        | Not Started |       |
+---------------+--------------------------------+-------------+-------+
| Code Quality  | ALL_TODOS_RESOLVED             | Not Started |       |
+---------------+--------------------------------+-------------+-------+
| Code Quality  | NO_TOOL_WARNINGS_THROWN        | Not Started |       |
+---------------+--------------------------------+-------------+-------+
| Code Quality  | TB_LINT_COMPLETE               | Not Started |       |
+---------------+--------------------------------+-------------+-------+
| Integration   | PRE_VERIFIED_SUB_MODULES_V3    | Not Started |       |
+---------------+--------------------------------+-------------+-------+
| Issues        | NO_ISSUES_PENDING              | Not Started |       |
+---------------+--------------------------------+-------------+-------+
| Review        | Reviewer(s)                    | Not Started |       |
+---------------+--------------------------------+-------------+-------+
| Review        | Signoff date                   | Not Started |       |
+---------------+--------------------------------+-------------+-------+

