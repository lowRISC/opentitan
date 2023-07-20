# Pin Multiplexer DIF Checklist

This checklist is for [Development Stage](../../../../doc/project_governance/development_stages.md) transitions for the [Pin Multiplexer DIF](../../../../hw/ip/pinmux/README.md).
All checklist items refer to the content in the [Checklist](../../../../doc/project_governance/checklist/README.md).

<h2>DIF Checklist</h2>

<h3>S1</h3>

Type           | Item                   | Resolution  | Note/Collaterals
---------------|------------------------|-------------|------------------
Implementation | [DIF_EXISTS][]         | Done        |
Implementation | [DIF_USED_IN_TREE][]   | Done        |
Tests          | [DIF_TEST_ON_DEVICE][] | Done        |

[DIF_EXISTS]:         ../../../../doc/project_governance/checklist/README.md#dif_exists
[DIF_USED_IN_TREE]:   ../../../../doc/project_governance/checklist/README.md#dif_used_in_tree
[DIF_TEST_ON_DEVICE]: ../../../../doc/project_governance/checklist/README.md#dif_test_on_device

<h3>S2</h3>

Type           | Item                        | Resolution  | Note/Collaterals
---------------|-----------------------------|-------------|------------------
Coordination   | [DIF_HW_FEATURE_COMPLETE][] | Done        | [HW Dashboard](../../../../hw/README.md)
Implementation | [DIF_FEATURES][]            | Done        |

[DIF_HW_FEATURE_COMPLETE]: ../../../../doc/project_governance/checklist/README.md#dif_hw_feature_complete
[DIF_FEATURES]:            ../../../../doc/project_governance/checklist/README.md#dif_features

<h3>S3</h3>

Type           | Item                             | Resolution  | Note/Collaterals
---------------|----------------------------------|-------------|------------------
Coordination   | [DIF_HW_DESIGN_COMPLETE][]       | Not Started |
Coordination   | [DIF_HW_VERIFICATION_COMPLETE][] | Not Started |
Documentation  | [DIF_DOC_HW][]                   | Not Started |
Code Quality   | [DIF_CODE_STYLE][]               | Not Started |
Tests          | [DIF_TEST_UNIT][]                | Done        |
Review         | [DIF_TODO_COMPLETE][]            | Not Started |
Review         | Reviewer(s)                      | Not Started |
Review         | Signoff date                     | Not Started |

[DIF_HW_DESIGN_COMPLETE]:       ../../../../doc/project_governance/checklist/README.md#dif_hw_design_complete
[DIF_HW_VERIFICATION_COMPLETE]: ../../../../doc/project_governance/checklist/README.md#dif_hw_verification_complete
[DIF_DOC_HW]:                   ../../../../doc/project_governance/checklist/README.md#dif_doc_hw
[DIF_CODE_STYLE]:               ../../../../doc/project_governance/checklist/README.md#dif_code_style
[DIF_TEST_UNIT]:                ../../../../doc/project_governance/checklist/README.md#dif_test_unit
[DIF_TODO_COMPLETE]:            ../../../../doc/project_governance/checklist/README.md#dif_todo_complete
