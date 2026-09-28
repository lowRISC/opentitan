# Ibex Processor Core Checklist

This checklist is for [Hardware Stage](../../../../../doc/project_governance/development_stages.md) transitions for the [Ibex Processor Core.](../README.md)
All checklist items refer to the content in the [Checklist.](../../../../../doc/project_governance/checklist/README.md)

## Design Checklist

### D1

Type          | Item                           | Resolution  | Note/Collaterals
--------------|--------------------------------|-------------|------------------
Documentation | [SPEC_COMPLETE][]              | Done        | [RV_CORE_IBEX Design Spec](../README.md)
Documentation | [CSR_DEFINED][]                | Done        | [Registers](registers.md)
RTL           | [CLKRST_CONNECTED][]           | Done        |
RTL           | [IP_TOP][]                     | Done        | rv_core_ibex.sv
RTL           | [IP_INSTANTIABLE][]            | Done        | Elaborates cleanly in EarlGrey
RTL           | [PHYSICAL_MACROS_DEFINED_80][] | Done        | ICache SRAMs via prim_ram_1p
RTL           | [FUNC_IMPLEMENTED][]           | Done        |
RTL           | [ASSERT_KNOWN_ADDED][]         | Done        |
Code Quality  | [LINT_SETUP][]                 | Done        |
Security      | [SEC_CM_SCOPED][]              | Done        | [Security countermeasures](interfaces.md#security-countermeasures)

[SPEC_COMPLETE]:              ../../../../../doc/project_governance/checklist/README.md#spec_complete
[CSR_DEFINED]:                ../../../../../doc/project_governance/checklist/README.md#csr_defined
[CLKRST_CONNECTED]:           ../../../../../doc/project_governance/checklist/README.md#clkrst_connected
[IP_TOP]:                     ../../../../../doc/project_governance/checklist/README.md#ip_top
[IP_INSTANTIABLE]:            ../../../../../doc/project_governance/checklist/README.md#ip_instantiable
[PHYSICAL_MACROS_DEFINED_80]: ../../../../../doc/project_governance/checklist/README.md#physical_macros_defined_80
[FUNC_IMPLEMENTED]:           ../../../../../doc/project_governance/checklist/README.md#func_implemented
[ASSERT_KNOWN_ADDED]:         ../../../../../doc/project_governance/checklist/README.md#assert_known_added
[LINT_SETUP]:                 ../../../../../doc/project_governance/checklist/README.md#lint_setup
[SEC_CM_SCOPED]:              ../../../../../doc/project_governance/checklist/README.md#sec_cm_scoped

### D2

Type          | Item                      | Resolution  | Note/Collaterals
--------------|---------------------------|-------------|------------------
Documentation | [NEW_FEATURES][]          | Not Started |
Documentation | [BLOCK_DIAGRAM][]         | Not Started |
Documentation | [DOC_INTERFACE][]         | Not Started |
Documentation | [DOC_INTEGRATION_D2][]    | Not Started |
Documentation | [MISSING_FUNC][]          | Not Started |
Documentation | [FEATURE_FROZEN][]        | Not Started |
RTL           | [FEATURE_COMPLETE][]      | Not Started |
RTL           | [PORT_FROZEN][]           | Not Started |
RTL           | [ARCHITECTURE_FROZEN][]   | Not Started |
RTL           | [REVIEW_TODO][]           | Not Started |
RTL           | [STYLE_X][]               | Not Started |
RTL           | [CDC_SYNCMACRO][]         | Not Started |
Code Quality  | [LINT_PASS][]             | Not Started |
Code Quality  | [CDC_SETUP][]             | Not Started |
Code Quality  | [RDC_SETUP][]             | Not Started |
Code Quality  | [AREA_CHECK][]            | Not Started |
Code Quality  | [TIMING_CHECK][]          | Not Started |
Security      | [SEC_CM_DOCUMENTED][]     | Not Started |

[NEW_FEATURES]:          ../../../../../doc/project_governance/checklist/README.md#new_features
[BLOCK_DIAGRAM]:         ../../../../../doc/project_governance/checklist/README.md#block_diagram
[DOC_INTERFACE]:         ../../../../../doc/project_governance/checklist/README.md#doc_interface
[DOC_INTEGRATION_D2]:    ../../../../../doc/project_governance/checklist/README.md#doc_integration_d2
[MISSING_FUNC]:          ../../../../../doc/project_governance/checklist/README.md#missing_func
[FEATURE_FROZEN]:        ../../../../../doc/project_governance/checklist/README.md#feature_frozen
[FEATURE_COMPLETE]:      ../../../../../doc/project_governance/checklist/README.md#feature_complete
[PORT_FROZEN]:           ../../../../../doc/project_governance/checklist/README.md#port_frozen
[ARCHITECTURE_FROZEN]:   ../../../../../doc/project_governance/checklist/README.md#architecture_frozen
[REVIEW_TODO]:           ../../../../../doc/project_governance/checklist/README.md#review_todo
[STYLE_X]:               ../../../../../doc/project_governance/checklist/README.md#style_x
[CDC_SYNCMACRO]:         ../../../../../doc/project_governance/checklist/README.md#cdc_syncmacro
[LINT_PASS]:             ../../../../../doc/project_governance/checklist/README.md#lint_pass
[CDC_SETUP]:             ../../../../../doc/project_governance/checklist/README.md#cdc_setup
[RDC_SETUP]:             ../../../../../doc/project_governance/checklist/README.md#rdc_setup
[AREA_CHECK]:            ../../../../../doc/project_governance/checklist/README.md#area_check
[TIMING_CHECK]:          ../../../../../doc/project_governance/checklist/README.md#timing_check
[SEC_CM_DOCUMENTED]:     ../../../../../doc/project_governance/checklist/README.md#sec_cm_documented

### D2S

 Type         | Item                         | Resolution  | Note/Collaterals
--------------|------------------------------|-------------|------------------
Security      | [SEC_CM_ASSETS_LISTED][]     | Not Started |
Security      | [SEC_CM_IMPLEMENTED][]       | Not Started |
Security      | [SEC_CM_RND_CNST][]          | Not Started |
Security      | [SEC_CM_NON_RESET_FLOPS][]   | Not Started |
Security      | [SEC_CM_SHADOW_REGS][]       | Not Started |
Security      | [SEC_CM_RTL_REVIEWED][]      | Not Started |
Security      | [SEC_CM_COUNCIL_REVIEWED][]  | Not Started |

[SEC_CM_ASSETS_LISTED]:    ../../../../../doc/project_governance/checklist/README.md#sec_cm_assets_listed
[SEC_CM_IMPLEMENTED]:      ../../../../../doc/project_governance/checklist/README.md#sec_cm_implemented
[SEC_CM_RND_CNST]:         ../../../../../doc/project_governance/checklist/README.md#sec_cm_rnd_cnst
[SEC_CM_NON_RESET_FLOPS]:  ../../../../../doc/project_governance/checklist/README.md#sec_cm_non_reset_flops
[SEC_CM_SHADOW_REGS]:      ../../../../../doc/project_governance/checklist/README.md#sec_cm_shadow_regs
[SEC_CM_RTL_REVIEWED]:     ../../../../../doc/project_governance/checklist/README.md#sec_cm_rtl_reviewed
[SEC_CM_COUNCIL_REVIEWED]: ../../../../../doc/project_governance/checklist/README.md#sec_cm_council_reviewed

### D3

 Type         | Item                    | Resolution  | Note/Collaterals
--------------|-------------------------|-------------|------------------
Documentation | [NEW_FEATURES_D3][]     | Not Started |
Documentation | [DOC_INTEGRATION_D3][]  | Not Started |
RTL           | [TODO_COMPLETE][]       | Not Started |
Code Quality  | [LINT_COMPLETE][]       | Not Started |
Code Quality  | [CDC_COMPLETE][]        | Not Started |
Code Quality  | [RDC_COMPLETE][]        | Not Started |
Review        | [REVIEW_RTL][]          | Not Started |
Review        | [REVIEW_DELETED_FF][]   | Not Started |
Review        | [REVIEW_SW_CHANGE][]    | Not Started |
Review        | [REVIEW_SW_ERRATA][]    | Not Started |
Review        | Reviewer(s)             | Not Started |
Review        | Signoff date            | Not Started |

[NEW_FEATURES_D3]:      ../../../../../doc/project_governance/checklist/README.md#new_features_d3
[DOC_INTEGRATION_D3]:   ../../../../../doc/project_governance/checklist/README.md#doc_integration_d3
[TODO_COMPLETE]:        ../../../../../doc/project_governance/checklist/README.md#todo_complete
[LINT_COMPLETE]:        ../../../../../doc/project_governance/checklist/README.md#lint_complete
[CDC_COMPLETE]:         ../../../../../doc/project_governance/checklist/README.md#cdc_complete
[RDC_COMPLETE]:         ../../../../../doc/project_governance/checklist/README.md#rdc_complete
[REVIEW_RTL]:           ../../../../../doc/project_governance/checklist/README.md#review_rtl
[REVIEW_DELETED_FF]:    ../../../../../doc/project_governance/checklist/README.md#review_deleted_ff
[REVIEW_SW_CHANGE]:     ../../../../../doc/project_governance/checklist/README.md#review_sw_change
[REVIEW_SW_ERRATA]:     ../../../../../doc/project_governance/checklist/README.md#review_sw_errata

## Verification Checklist

Ibex verification is tracked in the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/03_reference/verification_stages.html).
Ibex is at **V0**.

The verification checklist for the previously taped-out Ibex version (verification stage V2S, v2.1.0) used in Earl Grey v1.0.0 can be found in the [Ibex documentation tagged earlgrey_1.0.0](https://ibex-core.readthedocs.io/en/earlgrey_1.0.0/03_reference/verification_stages.html).

Features specific to rv_core_ibex do not have block-level verification.
Top-level testing suffices for these, see the [rv_core_ibex DV document](../dv/README.md) for more details.

### V1

The V1 checklist may be found in the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/03_reference/verification_stages.html#v1-checklist).

### V2

The V2 checklist may be found in the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/03_reference/verification_stages.html#v2-checklist).

### V2S

The V2S checklist may be found in the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/03_reference/verification_stages.html#v2s-checklist).

### V3

The V3 checklist may be found in the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/03_reference/verification_stages.html#v3-checklist).
