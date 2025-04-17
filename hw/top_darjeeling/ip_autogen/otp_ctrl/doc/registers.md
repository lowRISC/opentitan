# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/top_darjeeling/ip_autogen/otp_ctrl/data/otp_ctrl.hjson -->
## Summary

| Name                                                                           | Offset   |   Length | Description                                                                                         |
|:-------------------------------------------------------------------------------|:---------|---------:|:----------------------------------------------------------------------------------------------------|
| otp_ctrl.[`INTR_STATE`](#intr_state)                                           | 0x0      |        4 | Interrupt State Register                                                                            |
| otp_ctrl.[`INTR_ENABLE`](#intr_enable)                                         | 0x4      |        4 | Interrupt Enable Register                                                                           |
| otp_ctrl.[`INTR_TEST`](#intr_test)                                             | 0x8      |        4 | Interrupt Test Register                                                                             |
| otp_ctrl.[`ALERT_TEST`](#alert_test)                                           | 0xc      |        4 | Alert Test Register                                                                                 |
| otp_ctrl.[`STATUS`](#status)                                                   | 0x10     |        4 | OTP status register.                                                                                |
| otp_ctrl.[`ERR_CODE_0`](#err_code)                                             | 0x14     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_1`](#err_code)                                             | 0x18     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_2`](#err_code)                                             | 0x1c     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_3`](#err_code)                                             | 0x20     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_4`](#err_code)                                             | 0x24     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_5`](#err_code)                                             | 0x28     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_6`](#err_code)                                             | 0x2c     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_7`](#err_code)                                             | 0x30     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_8`](#err_code)                                             | 0x34     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_9`](#err_code)                                             | 0x38     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_10`](#err_code)                                            | 0x3c     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_11`](#err_code)                                            | 0x40     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_12`](#err_code)                                            | 0x44     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_13`](#err_code)                                            | 0x48     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_14`](#err_code)                                            | 0x4c     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_15`](#err_code)                                            | 0x50     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_16`](#err_code)                                            | 0x54     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_17`](#err_code)                                            | 0x58     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_18`](#err_code)                                            | 0x5c     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_19`](#err_code)                                            | 0x60     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_20`](#err_code)                                            | 0x64     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_21`](#err_code)                                            | 0x68     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_22`](#err_code)                                            | 0x6c     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`ERR_CODE_23`](#err_code)                                            | 0x70     |        4 | This register holds information about error conditions that occurred in the agents                  |
| otp_ctrl.[`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)                       | 0x74     |        4 | Register write enable for all direct access interface registers.                                    |
| otp_ctrl.[`DIRECT_ACCESS_CMD`](#direct_access_cmd)                             | 0x78     |        4 | Command register for direct accesses.                                                               |
| otp_ctrl.[`DIRECT_ACCESS_ADDRESS`](#direct_access_address)                     | 0x7c     |        4 | Address register for direct accesses.                                                               |
| otp_ctrl.[`DIRECT_ACCESS_WDATA_0`](#direct_access_wdata)                       | 0x80     |        4 | Write data for direct accesses.                                                                     |
| otp_ctrl.[`DIRECT_ACCESS_WDATA_1`](#direct_access_wdata)                       | 0x84     |        4 | Write data for direct accesses.                                                                     |
| otp_ctrl.[`DIRECT_ACCESS_RDATA_0`](#direct_access_rdata)                       | 0x88     |        4 | Read data for direct accesses.                                                                      |
| otp_ctrl.[`DIRECT_ACCESS_RDATA_1`](#direct_access_rdata)                       | 0x8c     |        4 | Read data for direct accesses.                                                                      |
| otp_ctrl.[`CHECK_TRIGGER_REGWEN`](#check_trigger_regwen)                       | 0x90     |        4 | Register write enable for !!CHECK_TRIGGER.                                                          |
| otp_ctrl.[`CHECK_TRIGGER`](#check_trigger)                                     | 0x94     |        4 | Command register for direct accesses.                                                               |
| otp_ctrl.[`CHECK_REGWEN`](#check_regwen)                                       | 0x98     |        4 | Register write enable for !!INTEGRITY_CHECK_PERIOD and !!CONSISTENCY_CHECK_PERIOD.                  |
| otp_ctrl.[`CHECK_TIMEOUT`](#check_timeout)                                     | 0x9c     |        4 | Timeout value for the integrity and consistency checks.                                             |
| otp_ctrl.[`INTEGRITY_CHECK_PERIOD`](#integrity_check_period)                   | 0xa0     |        4 | This value specifies the maximum period that can be generated pseudo-randomly.                      |
| otp_ctrl.[`CONSISTENCY_CHECK_PERIOD`](#consistency_check_period)               | 0xa4     |        4 | This value specifies the maximum period that can be generated pseudo-randomly.                      |
| otp_ctrl.[`VENDOR_TEST_READ_LOCK`](#vendor_test_read_lock)                     | 0xa8     |        4 | Runtime read lock for the VENDOR_TEST partition.                                                    |
| otp_ctrl.[`CREATOR_SW_CFG_READ_LOCK`](#creator_sw_cfg_read_lock)               | 0xac     |        4 | Runtime read lock for the CREATOR_SW_CFG partition.                                                 |
| otp_ctrl.[`OWNER_SW_CFG_READ_LOCK`](#owner_sw_cfg_read_lock)                   | 0xb0     |        4 | Runtime read lock for the OWNER_SW_CFG partition.                                                   |
| otp_ctrl.[`OWNERSHIP_SLOT_STATE_READ_LOCK`](#ownership_slot_state_read_lock)   | 0xb4     |        4 | Runtime read lock for the OWNERSHIP_SLOT_STATE partition.                                           |
| otp_ctrl.[`ROT_CREATOR_AUTH_READ_LOCK`](#rot_creator_auth_read_lock)           | 0xb8     |        4 | Runtime read lock for the ROT_CREATOR_AUTH partition.                                               |
| otp_ctrl.[`ROT_OWNER_AUTH_SLOT0_READ_LOCK`](#rot_owner_auth_slot0_read_lock)   | 0xbc     |        4 | Runtime read lock for the ROT_OWNER_AUTH_SLOT0 partition.                                           |
| otp_ctrl.[`ROT_OWNER_AUTH_SLOT1_READ_LOCK`](#rot_owner_auth_slot1_read_lock)   | 0xc0     |        4 | Runtime read lock for the ROT_OWNER_AUTH_SLOT1 partition.                                           |
| otp_ctrl.[`PLAT_INTEG_AUTH_SLOT0_READ_LOCK`](#plat_integ_auth_slot0_read_lock) | 0xc4     |        4 | Runtime read lock for the PLAT_INTEG_AUTH_SLOT0 partition.                                          |
| otp_ctrl.[`PLAT_INTEG_AUTH_SLOT1_READ_LOCK`](#plat_integ_auth_slot1_read_lock) | 0xc8     |        4 | Runtime read lock for the PLAT_INTEG_AUTH_SLOT1 partition.                                          |
| otp_ctrl.[`PLAT_OWNER_AUTH_SLOT0_READ_LOCK`](#plat_owner_auth_slot0_read_lock) | 0xcc     |        4 | Runtime read lock for the PLAT_OWNER_AUTH_SLOT0 partition.                                          |
| otp_ctrl.[`PLAT_OWNER_AUTH_SLOT1_READ_LOCK`](#plat_owner_auth_slot1_read_lock) | 0xd0     |        4 | Runtime read lock for the PLAT_OWNER_AUTH_SLOT1 partition.                                          |
| otp_ctrl.[`PLAT_OWNER_AUTH_SLOT2_READ_LOCK`](#plat_owner_auth_slot2_read_lock) | 0xd4     |        4 | Runtime read lock for the PLAT_OWNER_AUTH_SLOT2 partition.                                          |
| otp_ctrl.[`PLAT_OWNER_AUTH_SLOT3_READ_LOCK`](#plat_owner_auth_slot3_read_lock) | 0xd8     |        4 | Runtime read lock for the PLAT_OWNER_AUTH_SLOT3 partition.                                          |
| otp_ctrl.[`EXT_NVM_READ_LOCK`](#ext_nvm_read_lock)                             | 0xdc     |        4 | Runtime read lock for the EXT_NVM partition.                                                        |
| otp_ctrl.[`ROM_PATCH_READ_LOCK`](#rom_patch_read_lock)                         | 0xe0     |        4 | Runtime read lock for the ROM_PATCH partition.                                                      |
| otp_ctrl.[`VENDOR_TEST_DIGEST_0`](#vendor_test_digest)                         | 0xe4     |        4 | Integrity digest for the VENDOR_TEST partition.                                                     |
| otp_ctrl.[`VENDOR_TEST_DIGEST_1`](#vendor_test_digest)                         | 0xe8     |        4 | Integrity digest for the VENDOR_TEST partition.                                                     |
| otp_ctrl.[`CREATOR_SW_CFG_DIGEST_0`](#creator_sw_cfg_digest)                   | 0xec     |        4 | Integrity digest for the CREATOR_SW_CFG partition.                                                  |
| otp_ctrl.[`CREATOR_SW_CFG_DIGEST_1`](#creator_sw_cfg_digest)                   | 0xf0     |        4 | Integrity digest for the CREATOR_SW_CFG partition.                                                  |
| otp_ctrl.[`OWNER_SW_CFG_DIGEST_0`](#owner_sw_cfg_digest)                       | 0xf4     |        4 | Integrity digest for the OWNER_SW_CFG partition.                                                    |
| otp_ctrl.[`OWNER_SW_CFG_DIGEST_1`](#owner_sw_cfg_digest)                       | 0xf8     |        4 | Integrity digest for the OWNER_SW_CFG partition.                                                    |
| otp_ctrl.[`ROT_CREATOR_AUTH_DIGEST_0`](#rot_creator_auth_digest)               | 0xfc     |        4 | Integrity digest for the ROT_CREATOR_AUTH partition.                                                |
| otp_ctrl.[`ROT_CREATOR_AUTH_DIGEST_1`](#rot_creator_auth_digest)               | 0x100    |        4 | Integrity digest for the ROT_CREATOR_AUTH partition.                                                |
| otp_ctrl.[`ROT_OWNER_AUTH_SLOT0_DIGEST_0`](#rot_owner_auth_slot0_digest)       | 0x104    |        4 | Integrity digest for the ROT_OWNER_AUTH_SLOT0 partition.                                            |
| otp_ctrl.[`ROT_OWNER_AUTH_SLOT0_DIGEST_1`](#rot_owner_auth_slot0_digest)       | 0x108    |        4 | Integrity digest for the ROT_OWNER_AUTH_SLOT0 partition.                                            |
| otp_ctrl.[`ROT_OWNER_AUTH_SLOT1_DIGEST_0`](#rot_owner_auth_slot1_digest)       | 0x10c    |        4 | Integrity digest for the ROT_OWNER_AUTH_SLOT1 partition.                                            |
| otp_ctrl.[`ROT_OWNER_AUTH_SLOT1_DIGEST_1`](#rot_owner_auth_slot1_digest)       | 0x110    |        4 | Integrity digest for the ROT_OWNER_AUTH_SLOT1 partition.                                            |
| otp_ctrl.[`PLAT_INTEG_AUTH_SLOT0_DIGEST_0`](#plat_integ_auth_slot0_digest)     | 0x114    |        4 | Integrity digest for the PLAT_INTEG_AUTH_SLOT0 partition.                                           |
| otp_ctrl.[`PLAT_INTEG_AUTH_SLOT0_DIGEST_1`](#plat_integ_auth_slot0_digest)     | 0x118    |        4 | Integrity digest for the PLAT_INTEG_AUTH_SLOT0 partition.                                           |
| otp_ctrl.[`PLAT_INTEG_AUTH_SLOT1_DIGEST_0`](#plat_integ_auth_slot1_digest)     | 0x11c    |        4 | Integrity digest for the PLAT_INTEG_AUTH_SLOT1 partition.                                           |
| otp_ctrl.[`PLAT_INTEG_AUTH_SLOT1_DIGEST_1`](#plat_integ_auth_slot1_digest)     | 0x120    |        4 | Integrity digest for the PLAT_INTEG_AUTH_SLOT1 partition.                                           |
| otp_ctrl.[`PLAT_OWNER_AUTH_SLOT0_DIGEST_0`](#plat_owner_auth_slot0_digest)     | 0x124    |        4 | Integrity digest for the PLAT_OWNER_AUTH_SLOT0 partition.                                           |
| otp_ctrl.[`PLAT_OWNER_AUTH_SLOT0_DIGEST_1`](#plat_owner_auth_slot0_digest)     | 0x128    |        4 | Integrity digest for the PLAT_OWNER_AUTH_SLOT0 partition.                                           |
| otp_ctrl.[`PLAT_OWNER_AUTH_SLOT1_DIGEST_0`](#plat_owner_auth_slot1_digest)     | 0x12c    |        4 | Integrity digest for the PLAT_OWNER_AUTH_SLOT1 partition.                                           |
| otp_ctrl.[`PLAT_OWNER_AUTH_SLOT1_DIGEST_1`](#plat_owner_auth_slot1_digest)     | 0x130    |        4 | Integrity digest for the PLAT_OWNER_AUTH_SLOT1 partition.                                           |
| otp_ctrl.[`PLAT_OWNER_AUTH_SLOT2_DIGEST_0`](#plat_owner_auth_slot2_digest)     | 0x134    |        4 | Integrity digest for the PLAT_OWNER_AUTH_SLOT2 partition.                                           |
| otp_ctrl.[`PLAT_OWNER_AUTH_SLOT2_DIGEST_1`](#plat_owner_auth_slot2_digest)     | 0x138    |        4 | Integrity digest for the PLAT_OWNER_AUTH_SLOT2 partition.                                           |
| otp_ctrl.[`PLAT_OWNER_AUTH_SLOT3_DIGEST_0`](#plat_owner_auth_slot3_digest)     | 0x13c    |        4 | Integrity digest for the PLAT_OWNER_AUTH_SLOT3 partition.                                           |
| otp_ctrl.[`PLAT_OWNER_AUTH_SLOT3_DIGEST_1`](#plat_owner_auth_slot3_digest)     | 0x140    |        4 | Integrity digest for the PLAT_OWNER_AUTH_SLOT3 partition.                                           |
| otp_ctrl.[`ROM_PATCH_DIGEST_0`](#rom_patch_digest)                             | 0x144    |        4 | Integrity digest for the ROM_PATCH partition.                                                       |
| otp_ctrl.[`ROM_PATCH_DIGEST_1`](#rom_patch_digest)                             | 0x148    |        4 | Integrity digest for the ROM_PATCH partition.                                                       |
| otp_ctrl.[`HW_CFG0_DIGEST_0`](#hw_cfg0_digest)                                 | 0x14c    |        4 | Integrity digest for the HW_CFG0 partition.                                                         |
| otp_ctrl.[`HW_CFG0_DIGEST_1`](#hw_cfg0_digest)                                 | 0x150    |        4 | Integrity digest for the HW_CFG0 partition.                                                         |
| otp_ctrl.[`HW_CFG1_DIGEST_0`](#hw_cfg1_digest)                                 | 0x154    |        4 | Integrity digest for the HW_CFG1 partition.                                                         |
| otp_ctrl.[`HW_CFG1_DIGEST_1`](#hw_cfg1_digest)                                 | 0x158    |        4 | Integrity digest for the HW_CFG1 partition.                                                         |
| otp_ctrl.[`SECRET0_DIGEST_0`](#secret0_digest)                                 | 0x15c    |        4 | Integrity digest for the SECRET0 partition.                                                         |
| otp_ctrl.[`SECRET0_DIGEST_1`](#secret0_digest)                                 | 0x160    |        4 | Integrity digest for the SECRET0 partition.                                                         |
| otp_ctrl.[`SECRET1_DIGEST_0`](#secret1_digest)                                 | 0x164    |        4 | Integrity digest for the SECRET1 partition.                                                         |
| otp_ctrl.[`SECRET1_DIGEST_1`](#secret1_digest)                                 | 0x168    |        4 | Integrity digest for the SECRET1 partition.                                                         |
| otp_ctrl.[`SECRET2_DIGEST_0`](#secret2_digest)                                 | 0x16c    |        4 | Integrity digest for the SECRET2 partition.                                                         |
| otp_ctrl.[`SECRET2_DIGEST_1`](#secret2_digest)                                 | 0x170    |        4 | Integrity digest for the SECRET2 partition.                                                         |
| otp_ctrl.[`SECRET3_DIGEST_0`](#secret3_digest)                                 | 0x174    |        4 | Integrity digest for the SECRET3 partition.                                                         |
| otp_ctrl.[`SECRET3_DIGEST_1`](#secret3_digest)                                 | 0x178    |        4 | Integrity digest for the SECRET3 partition.                                                         |
| otp_ctrl.[`SW_CFG_WINDOW`](#sw_cfg_window)                                     | 0x4000   |    16384 | Any read to this window directly maps to the corresponding offset in the creator and owner software |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "otp_operation_done", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "otp_error", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                                                                      |
|:------:|:------:|:-------:|:-------------------|:-----------------------------------------------------------------------------------------------------------------|
|  31:2  |        |         |                    | Reserved                                                                                                         |
|   1    |  rw1c  |   0x0   | otp_error          | An error has occurred in the OTP controller. Check the [`ERR_CODE`](#err_code) register to get more information. |
|   0    |  rw1c  |   0x0   | otp_operation_done | A direct access command or digest calculation operation has completed.                                           |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "otp_operation_done", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "otp_error", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                                  |
|:------:|:------:|:-------:|:-------------------|:-----------------------------------------------------------------------------|
|  31:2  |        |         |                    | Reserved                                                                     |
|   1    |   rw   |   0x0   | otp_error          | Enable interrupt when [`INTR_STATE.otp_error`](#intr_state) is set.          |
|   0    |   rw   |   0x0   | otp_operation_done | Enable interrupt when [`INTR_STATE.otp_operation_done`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "otp_operation_done", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "otp_error", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                           |
|:------:|:------:|:-------:|:-------------------|:----------------------------------------------------------------------|
|  31:2  |        |         |                    | Reserved                                                              |
|   1    |   wo   |   0x0   | otp_error          | Write 1 to force [`INTR_STATE.otp_error`](#intr_state) to 1.          |
|   0    |   wo   |   0x0   | otp_operation_done | Write 1 to force [`INTR_STATE.otp_operation_done`](#intr_state) to 1. |

## ALERT_TEST
Alert Test Register
- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "fatal_macro_error", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_check_error", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_bus_integ_error", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "fatal_prim_otp_alert", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "recov_prim_otp_alert", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                      |
|:------:|:------:|:-------:|:----------------------|:-------------------------------------------------|
|  31:5  |        |         |                       | Reserved                                         |
|   4    |   wo   |   0x0   | recov_prim_otp_alert  | Write 1 to trigger one alert event of this kind. |
|   3    |   wo   |   0x0   | fatal_prim_otp_alert  | Write 1 to trigger one alert event of this kind. |
|   2    |   wo   |   0x0   | fatal_bus_integ_error | Write 1 to trigger one alert event of this kind. |
|   1    |   wo   |   0x0   | fatal_check_error     | Write 1 to trigger one alert event of this kind. |
|   0    |   wo   |   0x0   | fatal_macro_error     | Write 1 to trigger one alert event of this kind. |

## STATUS
OTP status register.
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0x7fffffff`

### Fields

```wavejson
{"reg": [{"name": "VENDOR_TEST_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CREATOR_SW_CFG_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "OWNER_SW_CFG_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "OWNERSHIP_SLOT_STATE_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ROT_CREATOR_AUTH_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ROT_OWNER_AUTH_SLOT0_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ROT_OWNER_AUTH_SLOT1_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "PLAT_INTEG_AUTH_SLOT0_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "PLAT_INTEG_AUTH_SLOT1_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "PLAT_OWNER_AUTH_SLOT0_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "PLAT_OWNER_AUTH_SLOT1_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "PLAT_OWNER_AUTH_SLOT2_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "PLAT_OWNER_AUTH_SLOT3_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "EXT_NVM_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ROM_PATCH_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "HW_CFG0_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "HW_CFG1_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SECRET0_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SECRET1_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SECRET2_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SECRET3_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "LIFE_CYCLE_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "DAI_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "LCI_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "TIMEOUT_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "LFSR_FSM_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SCRAMBLING_FSM_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "KEY_DERIV_FSM_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "BUS_INTEG_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "DAI_IDLE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CHECK_PENDING", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 1}], "config": {"lanes": 1, "fontsize": 10, "vspace": 290}}
```

|  Bits  |  Type  |  Reset  | Name                        | Description                                                                                                                                           |
|:------:|:------:|:-------:|:----------------------------|:------------------------------------------------------------------------------------------------------------------------------------------------------|
|   31   |        |         |                             | Reserved                                                                                                                                              |
|   30   |   ro   |   0x0   | CHECK_PENDING               | Set to 1 if an integrity or consistency check triggered by the LFSR timer or via [`CHECK_TRIGGER`](#check_trigger) is pending.                        |
|   29   |   ro   |   0x0   | DAI_IDLE                    | Set to 1 if the DAI is idle and ready to accept commands.                                                                                             |
|   28   |   ro   |   0x0   | BUS_INTEG_ERROR             | This bit is set to 1 if a fatal bus integrity fault is detected. This error triggers a fatal_bus_integ_error alert.                                   |
|   27   |   ro   |   0x0   | KEY_DERIV_FSM_ERROR         | Set to 1 if the key derivation FSM has reached an invalid state. This raises an fatal_check_error alert and is an unrecoverable error condition.      |
|   26   |   ro   |   0x0   | SCRAMBLING_FSM_ERROR        | Set to 1 if the scrambling datapath FSM has reached an invalid state. This raises an fatal_check_error alert and is an unrecoverable error condition. |
|   25   |   ro   |   0x0   | LFSR_FSM_ERROR              | Set to 1 if the LFSR timer FSM has reached an invalid state. This raises an fatal_check_error alert and is an unrecoverable error condition.          |
|   24   |   ro   |   0x0   | TIMEOUT_ERROR               | Set to 1 if an integrity or consistency check times out. This raises an fatal_check_error alert and is an unrecoverable error condition.              |
|   23   |   ro   |   0x0   | LCI_ERROR                   | Set to 1 if an error occurred in the LCI. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.               |
|   22   |   ro   |   0x0   | DAI_ERROR                   | Set to 1 if an error occurred in the DAI. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.               |
|   21   |   ro   |   0x0   | LIFE_CYCLE_ERROR            | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   20   |   ro   |   0x0   | SECRET3_ERROR               | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   19   |   ro   |   0x0   | SECRET2_ERROR               | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   18   |   ro   |   0x0   | SECRET1_ERROR               | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   17   |   ro   |   0x0   | SECRET0_ERROR               | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   16   |   ro   |   0x0   | HW_CFG1_ERROR               | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   15   |   ro   |   0x0   | HW_CFG0_ERROR               | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   14   |   ro   |   0x0   | ROM_PATCH_ERROR             | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   13   |   ro   |   0x0   | EXT_NVM_ERROR               | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   12   |   ro   |   0x0   | PLAT_OWNER_AUTH_SLOT3_ERROR | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   11   |   ro   |   0x0   | PLAT_OWNER_AUTH_SLOT2_ERROR | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   10   |   ro   |   0x0   | PLAT_OWNER_AUTH_SLOT1_ERROR | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   9    |   ro   |   0x0   | PLAT_OWNER_AUTH_SLOT0_ERROR | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   8    |   ro   |   0x0   | PLAT_INTEG_AUTH_SLOT1_ERROR | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   7    |   ro   |   0x0   | PLAT_INTEG_AUTH_SLOT0_ERROR | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   6    |   ro   |   0x0   | ROT_OWNER_AUTH_SLOT1_ERROR  | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   5    |   ro   |   0x0   | ROT_OWNER_AUTH_SLOT0_ERROR  | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   4    |   ro   |   0x0   | ROT_CREATOR_AUTH_ERROR      | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   3    |   ro   |   0x0   | OWNERSHIP_SLOT_STATE_ERROR  | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   2    |   ro   |   0x0   | OWNER_SW_CFG_ERROR          | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   1    |   ro   |   0x0   | CREATOR_SW_CFG_ERROR        | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |
|   0    |   ro   |   0x0   | VENDOR_TEST_ERROR           | Set to 1 if an error occurred in this partition. If set to 1, SW should check the [`ERR_CODE`](#err_code) register at the corresponding index.        |

## ERR_CODE
This register holds information about error conditions that occurred in the agents
interacting with the OTP macro via the internal bus. The error codes should be checked
if the partitions, DAI or LCI flag an error in the [`STATUS`](#status) register, or when an
[`INTR_STATE.otp_error`](#intr_state) has been triggered. Note that all errors trigger an otp_error
interrupt, and in addition some errors may trigger either an fatal_macro_error or an
fatal_check_error alert.
- Reset default: `0x0`
- Reset mask: `0x7`

### Instances

| Name        | Offset   |
|:------------|:---------|
| ERR_CODE_0  | 0x14     |
| ERR_CODE_1  | 0x18     |
| ERR_CODE_2  | 0x1c     |
| ERR_CODE_3  | 0x20     |
| ERR_CODE_4  | 0x24     |
| ERR_CODE_5  | 0x28     |
| ERR_CODE_6  | 0x2c     |
| ERR_CODE_7  | 0x30     |
| ERR_CODE_8  | 0x34     |
| ERR_CODE_9  | 0x38     |
| ERR_CODE_10 | 0x3c     |
| ERR_CODE_11 | 0x40     |
| ERR_CODE_12 | 0x44     |
| ERR_CODE_13 | 0x48     |
| ERR_CODE_14 | 0x4c     |
| ERR_CODE_15 | 0x50     |
| ERR_CODE_16 | 0x54     |
| ERR_CODE_17 | 0x58     |
| ERR_CODE_18 | 0x5c     |
| ERR_CODE_19 | 0x60     |
| ERR_CODE_20 | 0x64     |
| ERR_CODE_21 | 0x68     |
| ERR_CODE_22 | 0x6c     |
| ERR_CODE_23 | 0x70     |


### Fields

```wavejson
{"reg": [{"name": "ERR_CODE", "bits": 3, "attr": ["ro"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name                            |
|:------:|:------:|:-------:|:--------------------------------|
|  31:3  |        |         | Reserved                        |
|  2:0   |   ro   |   0x0   | [ERR_CODE](#err_code--err_code) |

### ERR_CODE . ERR_CODE

| Value   | Name                    | Description                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |
|:--------|:------------------------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 0x0     | NO_ERROR                | No error condition has occurred.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| 0x1     | MACRO_ERROR             | Returned if the OTP macro command was invalid or did not complete successfully due to a macro malfunction. This error should never occur during normal operation and is not recoverable. This error triggers an fatal_macro_error alert.                                                                                                                                                                                                                                                                                                                                                                             |
| 0x2     | MACRO_ECC_CORR_ERROR    | A correctable ECC error has occured during an OTP read operation. The corresponding controller automatically recovers from this error when issuing a new command.                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| 0x3     | MACRO_ECC_UNCORR_ERROR  | An uncorrectable ECC error has occurred during an OTP read operation. This error should never occur during normal operation and is not recoverable. If this error is present this may be a sign that the device is malfunctioning. This error triggers an fatal_macro_error alert.                                                                                                                                                                                                                                                                                                                                   |
| 0x4     | MACRO_WRITE_BLANK_ERROR | This error is returned if a programming operation attempted to clear a bit that has previously been programmed to 1. The corresponding controller automatically recovers from this error when issuing a new command. Note however that the affected OTP word may be left in an inconsistent state if this error occurs. This can cause several issues when the word is accessed again (either as part of a regular read operation, as part of the readout at boot, or as part of a background check). It is important that SW ensures that each word is only written once, since this can render the device useless. |
| 0x5     | ACCESS_ERROR            | This error indicates that a locked memory region has been accessed. The corresponding controller automatically recovers from this error when issuing a new command.                                                                                                                                                                                                                                                                                                                                                                                                                                                  |
| 0x6     | CHECK_FAIL_ERROR        | An ECC, integrity or consistency mismatch has been detected in the buffer registers. This error should never occur during normal operation and is not recoverable. This error triggers an fatal_check_error alert.                                                                                                                                                                                                                                                                                                                                                                                                   |
| 0x7     | FSM_STATE_ERROR         | The FSM of the corresponding controller has reached an invalid state, or the FSM has been moved into a terminal error state due to an escalation action via lc_escalate_en_i. This error should never occur during normal operation and is not recoverable. If this error is present, this is a sign that the device has fallen victim to an invasive attack. This error triggers an fatal_check_error alert.                                                                                                                                                                                                        |


## DIRECT_ACCESS_REGWEN
Register write enable for all direct access interface registers.
- Offset: `0x74`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "DIRECT_ACCESS_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                                                                |
|:------:|:------:|:-------:|:--------------------------------------------------------------------|
|  31:1  |        |         | Reserved                                                            |
|   0    |  rw0c  |   0x1   | [DIRECT_ACCESS_REGWEN](#direct_access_regwen--direct_access_regwen) |

### DIRECT_ACCESS_REGWEN . DIRECT_ACCESS_REGWEN
This bit controls whether the DAI registers can be written.
Write 0 to it in order to clear the bit.

Note that the hardware also modulates this bit and sets it to 0 temporarily
during an OTP operation such that the corresponding address and data registers
cannot be modified while an operation is pending. The [`DAI_IDLE`](#dai_idle) status bit
will also be set to 0 in such a case.

## DIRECT_ACCESS_CMD
Command register for direct accesses.
- Offset: `0x78`
- Reset default: `0x0`
- Reset mask: `0x7`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "RD", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"name": "WR", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"name": "DIGEST", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                                                                                                                |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:3  |        |         |        | Reserved                                                                                                                                                                                                                                                                                   |
|   2    | r0w1c  |   0x0   | DIGEST | Initiates the digest calculation and locking sequence for the partition specified by [`DIRECT_ACCESS_ADDRESS.`](#direct_access_address)                                                                                                                                                    |
|   1    | r0w1c  |   0x0   | WR     | Initiates a programming sequence that writes the data in [`DIRECT_ACCESS_WDATA_0`](#direct_access_wdata_0) and [`DIRECT_ACCESS_WDATA_1`](#direct_access_wdata_1) (for 64bit partitions) to the location specified by [`DIRECT_ACCESS_ADDRESS.`](#direct_access_address)                    |
|   0    | r0w1c  |   0x0   | RD     | Initiates a readout sequence that reads the location specified by [`DIRECT_ACCESS_ADDRESS.`](#direct_access_address) The command places the data read into [`DIRECT_ACCESS_RDATA_0`](#direct_access_rdata_0) and [`DIRECT_ACCESS_RDATA_1`](#direct_access_rdata_1) (for 64bit partitions). |

## DIRECT_ACCESS_ADDRESS
Address register for direct accesses.
- Offset: `0x7c`
- Reset default: `0x0`
- Reset mask: `0x3fff`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "DIRECT_ACCESS_ADDRESS", "bits": 14, "attr": ["rw"], "rotate": 0}, {"bits": 18}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                                   |
|:------:|:------:|:-------:|:-----------------------------------------------------------------------|
| 31:14  |        |         | Reserved                                                               |
|  13:0  |   rw   |   0x0   | [DIRECT_ACCESS_ADDRESS](#direct_access_address--direct_access_address) |

### DIRECT_ACCESS_ADDRESS . DIRECT_ACCESS_ADDRESS
This is the address for the OTP word to be read or written through
the direct access interface. Note that the address is aligned to the access size
internally, hence bits 1:0 are ignored for 32bit accesses, and bits 2:0 are ignored
for 64bit accesses.

For the digest calculation command, set this register to the partition base offset.

## DIRECT_ACCESS_WDATA
Write data for direct accesses.
Hardware automatically determines the access granule (32bit or 64bit) based on which
partition is being written to.
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Instances

| Name                  | Offset   |
|:----------------------|:---------|
| DIRECT_ACCESS_WDATA_0 | 0x80     |
| DIRECT_ACCESS_WDATA_1 | 0x84     |


### Fields

```wavejson
{"reg": [{"name": "DIRECT_ACCESS_WDATA", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                | Description   |
|:------:|:------:|:-------:|:--------------------|:--------------|
|  31:0  |   rw   |   0x0   | DIRECT_ACCESS_WDATA |               |

## DIRECT_ACCESS_RDATA
Read data for direct accesses.
Hardware automatically determines the access granule (32bit or 64bit) based on which
partition is read from.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                  | Offset   |
|:----------------------|:---------|
| DIRECT_ACCESS_RDATA_0 | 0x88     |
| DIRECT_ACCESS_RDATA_1 | 0x8c     |


### Fields

```wavejson
{"reg": [{"name": "DIRECT_ACCESS_RDATA", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                | Description   |
|:------:|:------:|:-------:|:--------------------|:--------------|
|  31:0  |   ro   |   0x0   | DIRECT_ACCESS_RDATA |               |

## CHECK_TRIGGER_REGWEN
Register write enable for [`CHECK_TRIGGER.`](#check_trigger)
- Offset: `0x90`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "CHECK_TRIGGER_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                                             |
|:------:|:------:|:-------:|:---------------------|:------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                      | Reserved                                                                                                                |
|   0    |  rw0c  |   0x1   | CHECK_TRIGGER_REGWEN | When cleared to 0, the [`CHECK_TRIGGER`](#check_trigger) register cannot be written anymore. Write 0 to clear this bit. |

## CHECK_TRIGGER
Command register for direct accesses.
- Offset: `0x94`
- Reset default: `0x0`
- Reset mask: `0x3`
- Register enable: [`CHECK_TRIGGER_REGWEN`](#check_trigger_regwen)

### Fields

```wavejson
{"reg": [{"name": "INTEGRITY", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"name": "CONSISTENCY", "bits": 1, "attr": ["r0w1c"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name                                       |
|:------:|:------:|:-------:|:-------------------------------------------|
|  31:2  |        |         | Reserved                                   |
|   1    | r0w1c  |   0x0   | [CONSISTENCY](#check_trigger--consistency) |
|   0    | r0w1c  |   0x0   | [INTEGRITY](#check_trigger--integrity)     |

### CHECK_TRIGGER . CONSISTENCY
Writing 1 to this bit triggers a consistency check. SW should monitor [`STATUS.CHECK_PENDING`](#status)
and wait until the check has been completed. If there are any errors, those will be flagged
in the [`STATUS`](#status) and [`ERR_CODE`](#err_code) registers, and via interrupts and alerts.

### CHECK_TRIGGER . INTEGRITY
Writing 1 to this bit triggers an integrity check. SW should monitor [`STATUS.CHECK_PENDING`](#status)
and wait until the check has been completed. If there are any errors, those will be flagged
in the [`STATUS`](#status) and [`ERR_CODE`](#err_code) registers, and via the interrupts and alerts.

## CHECK_REGWEN
Register write enable for [`INTEGRITY_CHECK_PERIOD`](#integrity_check_period) and [`CONSISTENCY_CHECK_PERIOD.`](#consistency_check_period)
- Offset: `0x98`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "CHECK_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                                                                                                                                                                        |
|:------:|:------:|:-------:|:-------------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |              | Reserved                                                                                                                                                                                           |
|   0    |  rw0c  |   0x1   | CHECK_REGWEN | When cleared to 0, [`INTEGRITY_CHECK_PERIOD`](#integrity_check_period) and [`CONSISTENCY_CHECK_PERIOD`](#consistency_check_period) registers cannot be written anymore. Write 0 to clear this bit. |

## CHECK_TIMEOUT
Timeout value for the integrity and consistency checks.
- Offset: `0x9c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CHECK_REGWEN`](#check_regwen)

### Fields

```wavejson
{"reg": [{"name": "CHECK_TIMEOUT", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                           |
|:------:|:------:|:-------:|:-----------------------------------------------|
|  31:0  |   rw   |   0x0   | [CHECK_TIMEOUT](#check_timeout--check_timeout) |

### CHECK_TIMEOUT . CHECK_TIMEOUT
Timeout value in cycles for the for the integrity and consistency checks. If an integrity or consistency
check does not complete within the timeout window, an error will be flagged in the [`STATUS`](#status) register,
an otp_error interrupt will be raised, and an fatal_check_error alert will be sent out. The timeout should
be set to a large value to stay on the safe side. The maximum check time can be upper bounded by the
number of cycles it takes to readout, scramble and digest the entire OTP array. Since this amounts to
roughly 25k cycles, it is recommended to set this value to at least 100'000 cycles in order to stay on the
safe side. A value of zero disables the timeout mechanism (default).

## INTEGRITY_CHECK_PERIOD
This value specifies the maximum period that can be generated pseudo-randomly.
Only applies to the HW_CFG* and SECRET* partitions once they are locked.
- Offset: `0xa0`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CHECK_REGWEN`](#check_regwen)

### Fields

```wavejson
{"reg": [{"name": "INTEGRITY_CHECK_PERIOD", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                                      |
|:------:|:------:|:-------:|:--------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | [INTEGRITY_CHECK_PERIOD](#integrity_check_period--integrity_check_period) |

### INTEGRITY_CHECK_PERIOD . INTEGRITY_CHECK_PERIOD
The pseudo-random period is generated using a 40bit LFSR internally, and this register defines
the bit mask to be applied to the LFSR output in order to limit its range. The value of this
register is left shifted by 8bits and the lower bits are set to 8'hFF in order to form the 40bit mask.
A recommended value is 0x3_FFFF, corresponding to a maximum period of ~2.8s at 24MHz.
A value of zero disables the timer (default). Note that a one-off check can always be triggered via
[`CHECK_TRIGGER.INTEGRITY.`](#check_trigger)

## CONSISTENCY_CHECK_PERIOD
This value specifies the maximum period that can be generated pseudo-randomly.
This applies to the LIFE_CYCLE partition and the HW_CFG* and SECRET* partitions once they are locked.
- Offset: `0xa4`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CHECK_REGWEN`](#check_regwen)

### Fields

```wavejson
{"reg": [{"name": "CONSISTENCY_CHECK_PERIOD", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                                                            |
|:------:|:------:|:-------:|:--------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | [CONSISTENCY_CHECK_PERIOD](#consistency_check_period--consistency_check_period) |

### CONSISTENCY_CHECK_PERIOD . CONSISTENCY_CHECK_PERIOD
The pseudo-random period is generated using a 40bit LFSR internally, and this register defines
the bit mask to be applied to the LFSR output in order to limit its range. The value of this
register is left shifted by 8bits and the lower bits are set to 8'hFF in order to form the 40bit mask.
A recommended value is 0x3FF_FFFF, corresponding to a maximum period of ~716s at 24MHz.
A value of zero disables the timer (default). Note that a one-off check can always be triggered via
[`CHECK_TRIGGER.CONSISTENCY.`](#check_trigger)

## VENDOR_TEST_READ_LOCK
Runtime read lock for the VENDOR_TEST partition.
- Offset: `0xa8`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "VENDOR_TEST_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                                                                       |
|:------:|:------:|:-------:|:----------------------|:--------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                       | Reserved                                                                                          |
|   0    |  rw0c  |   0x1   | VENDOR_TEST_READ_LOCK | When cleared to 0, read access to the VENDOR_TEST partition is locked. Write 0 to clear this bit. |

## CREATOR_SW_CFG_READ_LOCK
Runtime read lock for the CREATOR_SW_CFG partition.
- Offset: `0xac`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "CREATOR_SW_CFG_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 260}}
```

|  Bits  |  Type  |  Reset  | Name                     | Description                                                                                          |
|:------:|:------:|:-------:|:-------------------------|:-----------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                          | Reserved                                                                                             |
|   0    |  rw0c  |   0x1   | CREATOR_SW_CFG_READ_LOCK | When cleared to 0, read access to the CREATOR_SW_CFG partition is locked. Write 0 to clear this bit. |

## OWNER_SW_CFG_READ_LOCK
Runtime read lock for the OWNER_SW_CFG partition.
- Offset: `0xb0`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "OWNER_SW_CFG_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 240}}
```

|  Bits  |  Type  |  Reset  | Name                   | Description                                                                                        |
|:------:|:------:|:-------:|:-----------------------|:---------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                        | Reserved                                                                                           |
|   0    |  rw0c  |   0x1   | OWNER_SW_CFG_READ_LOCK | When cleared to 0, read access to the OWNER_SW_CFG partition is locked. Write 0 to clear this bit. |

## OWNERSHIP_SLOT_STATE_READ_LOCK
Runtime read lock for the OWNERSHIP_SLOT_STATE partition.
- Offset: `0xb4`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "OWNERSHIP_SLOT_STATE_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 320}}
```

|  Bits  |  Type  |  Reset  | Name                           | Description                                                                                                |
|:------:|:------:|:-------:|:-------------------------------|:-----------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                                | Reserved                                                                                                   |
|   0    |  rw0c  |   0x1   | OWNERSHIP_SLOT_STATE_READ_LOCK | When cleared to 0, read access to the OWNERSHIP_SLOT_STATE partition is locked. Write 0 to clear this bit. |

## ROT_CREATOR_AUTH_READ_LOCK
Runtime read lock for the ROT_CREATOR_AUTH partition.
- Offset: `0xb8`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "ROT_CREATOR_AUTH_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 280}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                                                            |
|:------:|:------:|:-------:|:---------------------------|:-------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                            | Reserved                                                                                               |
|   0    |  rw0c  |   0x1   | ROT_CREATOR_AUTH_READ_LOCK | When cleared to 0, read access to the ROT_CREATOR_AUTH partition is locked. Write 0 to clear this bit. |

## ROT_OWNER_AUTH_SLOT0_READ_LOCK
Runtime read lock for the ROT_OWNER_AUTH_SLOT0 partition.
- Offset: `0xbc`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "ROT_OWNER_AUTH_SLOT0_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 320}}
```

|  Bits  |  Type  |  Reset  | Name                           | Description                                                                                                |
|:------:|:------:|:-------:|:-------------------------------|:-----------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                                | Reserved                                                                                                   |
|   0    |  rw0c  |   0x1   | ROT_OWNER_AUTH_SLOT0_READ_LOCK | When cleared to 0, read access to the ROT_OWNER_AUTH_SLOT0 partition is locked. Write 0 to clear this bit. |

## ROT_OWNER_AUTH_SLOT1_READ_LOCK
Runtime read lock for the ROT_OWNER_AUTH_SLOT1 partition.
- Offset: `0xc0`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "ROT_OWNER_AUTH_SLOT1_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 320}}
```

|  Bits  |  Type  |  Reset  | Name                           | Description                                                                                                |
|:------:|:------:|:-------:|:-------------------------------|:-----------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                                | Reserved                                                                                                   |
|   0    |  rw0c  |   0x1   | ROT_OWNER_AUTH_SLOT1_READ_LOCK | When cleared to 0, read access to the ROT_OWNER_AUTH_SLOT1 partition is locked. Write 0 to clear this bit. |

## PLAT_INTEG_AUTH_SLOT0_READ_LOCK
Runtime read lock for the PLAT_INTEG_AUTH_SLOT0 partition.
- Offset: `0xc4`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "PLAT_INTEG_AUTH_SLOT0_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 330}}
```

|  Bits  |  Type  |  Reset  | Name                            | Description                                                                                                 |
|:------:|:------:|:-------:|:--------------------------------|:------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                                 | Reserved                                                                                                    |
|   0    |  rw0c  |   0x1   | PLAT_INTEG_AUTH_SLOT0_READ_LOCK | When cleared to 0, read access to the PLAT_INTEG_AUTH_SLOT0 partition is locked. Write 0 to clear this bit. |

## PLAT_INTEG_AUTH_SLOT1_READ_LOCK
Runtime read lock for the PLAT_INTEG_AUTH_SLOT1 partition.
- Offset: `0xc8`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "PLAT_INTEG_AUTH_SLOT1_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 330}}
```

|  Bits  |  Type  |  Reset  | Name                            | Description                                                                                                 |
|:------:|:------:|:-------:|:--------------------------------|:------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                                 | Reserved                                                                                                    |
|   0    |  rw0c  |   0x1   | PLAT_INTEG_AUTH_SLOT1_READ_LOCK | When cleared to 0, read access to the PLAT_INTEG_AUTH_SLOT1 partition is locked. Write 0 to clear this bit. |

## PLAT_OWNER_AUTH_SLOT0_READ_LOCK
Runtime read lock for the PLAT_OWNER_AUTH_SLOT0 partition.
- Offset: `0xcc`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "PLAT_OWNER_AUTH_SLOT0_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 330}}
```

|  Bits  |  Type  |  Reset  | Name                            | Description                                                                                                 |
|:------:|:------:|:-------:|:--------------------------------|:------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                                 | Reserved                                                                                                    |
|   0    |  rw0c  |   0x1   | PLAT_OWNER_AUTH_SLOT0_READ_LOCK | When cleared to 0, read access to the PLAT_OWNER_AUTH_SLOT0 partition is locked. Write 0 to clear this bit. |

## PLAT_OWNER_AUTH_SLOT1_READ_LOCK
Runtime read lock for the PLAT_OWNER_AUTH_SLOT1 partition.
- Offset: `0xd0`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "PLAT_OWNER_AUTH_SLOT1_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 330}}
```

|  Bits  |  Type  |  Reset  | Name                            | Description                                                                                                 |
|:------:|:------:|:-------:|:--------------------------------|:------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                                 | Reserved                                                                                                    |
|   0    |  rw0c  |   0x1   | PLAT_OWNER_AUTH_SLOT1_READ_LOCK | When cleared to 0, read access to the PLAT_OWNER_AUTH_SLOT1 partition is locked. Write 0 to clear this bit. |

## PLAT_OWNER_AUTH_SLOT2_READ_LOCK
Runtime read lock for the PLAT_OWNER_AUTH_SLOT2 partition.
- Offset: `0xd4`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "PLAT_OWNER_AUTH_SLOT2_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 330}}
```

|  Bits  |  Type  |  Reset  | Name                            | Description                                                                                                 |
|:------:|:------:|:-------:|:--------------------------------|:------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                                 | Reserved                                                                                                    |
|   0    |  rw0c  |   0x1   | PLAT_OWNER_AUTH_SLOT2_READ_LOCK | When cleared to 0, read access to the PLAT_OWNER_AUTH_SLOT2 partition is locked. Write 0 to clear this bit. |

## PLAT_OWNER_AUTH_SLOT3_READ_LOCK
Runtime read lock for the PLAT_OWNER_AUTH_SLOT3 partition.
- Offset: `0xd8`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "PLAT_OWNER_AUTH_SLOT3_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 330}}
```

|  Bits  |  Type  |  Reset  | Name                            | Description                                                                                                 |
|:------:|:------:|:-------:|:--------------------------------|:------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                                 | Reserved                                                                                                    |
|   0    |  rw0c  |   0x1   | PLAT_OWNER_AUTH_SLOT3_READ_LOCK | When cleared to 0, read access to the PLAT_OWNER_AUTH_SLOT3 partition is locked. Write 0 to clear this bit. |

## EXT_NVM_READ_LOCK
Runtime read lock for the EXT_NVM partition.
- Offset: `0xdc`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "EXT_NVM_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                                                                                   |
|:------:|:------:|:-------:|:------------------|:----------------------------------------------------------------------------------------------|
|  31:1  |        |         |                   | Reserved                                                                                      |
|   0    |  rw0c  |   0x1   | EXT_NVM_READ_LOCK | When cleared to 0, read access to the EXT_NVM partition is locked. Write 0 to clear this bit. |

## ROM_PATCH_READ_LOCK
Runtime read lock for the ROM_PATCH partition.
- Offset: `0xe0`
- Reset default: `0x1`
- Reset mask: `0x1`
- Register enable: [`DIRECT_ACCESS_REGWEN`](#direct_access_regwen)

### Fields

```wavejson
{"reg": [{"name": "ROM_PATCH_READ_LOCK", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 210}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                                                                                     |
|:------:|:------:|:-------:|:--------------------|:------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                     | Reserved                                                                                        |
|   0    |  rw0c  |   0x1   | ROM_PATCH_READ_LOCK | When cleared to 0, read access to the ROM_PATCH partition is locked. Write 0 to clear this bit. |

## VENDOR_TEST_DIGEST
Integrity digest for the VENDOR_TEST partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the VENDOR_TEST partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                 | Offset   |
|:---------------------|:---------|
| VENDOR_TEST_DIGEST_0 | 0xe4     |
| VENDOR_TEST_DIGEST_1 | 0xe8     |


### Fields

```wavejson
{"reg": [{"name": "VENDOR_TEST_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name               | Description   |
|:------:|:------:|:-------:|:-------------------|:--------------|
|  31:0  |   ro   |   0x0   | VENDOR_TEST_DIGEST |               |

## CREATOR_SW_CFG_DIGEST
Integrity digest for the CREATOR_SW_CFG partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the CREATOR_SW_CFG partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                    | Offset   |
|:------------------------|:---------|
| CREATOR_SW_CFG_DIGEST_0 | 0xec     |
| CREATOR_SW_CFG_DIGEST_1 | 0xf0     |


### Fields

```wavejson
{"reg": [{"name": "CREATOR_SW_CFG_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description   |
|:------:|:------:|:-------:|:----------------------|:--------------|
|  31:0  |   ro   |   0x0   | CREATOR_SW_CFG_DIGEST |               |

## OWNER_SW_CFG_DIGEST
Integrity digest for the OWNER_SW_CFG partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the OWNER_SW_CFG partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                  | Offset   |
|:----------------------|:---------|
| OWNER_SW_CFG_DIGEST_0 | 0xf4     |
| OWNER_SW_CFG_DIGEST_1 | 0xf8     |


### Fields

```wavejson
{"reg": [{"name": "OWNER_SW_CFG_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                | Description   |
|:------:|:------:|:-------:|:--------------------|:--------------|
|  31:0  |   ro   |   0x0   | OWNER_SW_CFG_DIGEST |               |

## ROT_CREATOR_AUTH_DIGEST
Integrity digest for the ROT_CREATOR_AUTH partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the ROT_CREATOR_AUTH partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                      | Offset   |
|:--------------------------|:---------|
| ROT_CREATOR_AUTH_DIGEST_0 | 0xfc     |
| ROT_CREATOR_AUTH_DIGEST_1 | 0x100    |


### Fields

```wavejson
{"reg": [{"name": "ROT_CREATOR_AUTH_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                    | Description   |
|:------:|:------:|:-------:|:------------------------|:--------------|
|  31:0  |   ro   |   0x0   | ROT_CREATOR_AUTH_DIGEST |               |

## ROT_OWNER_AUTH_SLOT0_DIGEST
Integrity digest for the ROT_OWNER_AUTH_SLOT0 partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the ROT_OWNER_AUTH_SLOT0 partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                          | Offset   |
|:------------------------------|:---------|
| ROT_OWNER_AUTH_SLOT0_DIGEST_0 | 0x104    |
| ROT_OWNER_AUTH_SLOT0_DIGEST_1 | 0x108    |


### Fields

```wavejson
{"reg": [{"name": "ROT_OWNER_AUTH_SLOT0_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                        | Description   |
|:------:|:------:|:-------:|:----------------------------|:--------------|
|  31:0  |   ro   |   0x0   | ROT_OWNER_AUTH_SLOT0_DIGEST |               |

## ROT_OWNER_AUTH_SLOT1_DIGEST
Integrity digest for the ROT_OWNER_AUTH_SLOT1 partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the ROT_OWNER_AUTH_SLOT1 partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                          | Offset   |
|:------------------------------|:---------|
| ROT_OWNER_AUTH_SLOT1_DIGEST_0 | 0x10c    |
| ROT_OWNER_AUTH_SLOT1_DIGEST_1 | 0x110    |


### Fields

```wavejson
{"reg": [{"name": "ROT_OWNER_AUTH_SLOT1_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                        | Description   |
|:------:|:------:|:-------:|:----------------------------|:--------------|
|  31:0  |   ro   |   0x0   | ROT_OWNER_AUTH_SLOT1_DIGEST |               |

## PLAT_INTEG_AUTH_SLOT0_DIGEST
Integrity digest for the PLAT_INTEG_AUTH_SLOT0 partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the PLAT_INTEG_AUTH_SLOT0 partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                           | Offset   |
|:-------------------------------|:---------|
| PLAT_INTEG_AUTH_SLOT0_DIGEST_0 | 0x114    |
| PLAT_INTEG_AUTH_SLOT0_DIGEST_1 | 0x118    |


### Fields

```wavejson
{"reg": [{"name": "PLAT_INTEG_AUTH_SLOT0_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                         | Description   |
|:------:|:------:|:-------:|:-----------------------------|:--------------|
|  31:0  |   ro   |   0x0   | PLAT_INTEG_AUTH_SLOT0_DIGEST |               |

## PLAT_INTEG_AUTH_SLOT1_DIGEST
Integrity digest for the PLAT_INTEG_AUTH_SLOT1 partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the PLAT_INTEG_AUTH_SLOT1 partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                           | Offset   |
|:-------------------------------|:---------|
| PLAT_INTEG_AUTH_SLOT1_DIGEST_0 | 0x11c    |
| PLAT_INTEG_AUTH_SLOT1_DIGEST_1 | 0x120    |


### Fields

```wavejson
{"reg": [{"name": "PLAT_INTEG_AUTH_SLOT1_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                         | Description   |
|:------:|:------:|:-------:|:-----------------------------|:--------------|
|  31:0  |   ro   |   0x0   | PLAT_INTEG_AUTH_SLOT1_DIGEST |               |

## PLAT_OWNER_AUTH_SLOT0_DIGEST
Integrity digest for the PLAT_OWNER_AUTH_SLOT0 partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the PLAT_OWNER_AUTH_SLOT0 partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                           | Offset   |
|:-------------------------------|:---------|
| PLAT_OWNER_AUTH_SLOT0_DIGEST_0 | 0x124    |
| PLAT_OWNER_AUTH_SLOT0_DIGEST_1 | 0x128    |


### Fields

```wavejson
{"reg": [{"name": "PLAT_OWNER_AUTH_SLOT0_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                         | Description   |
|:------:|:------:|:-------:|:-----------------------------|:--------------|
|  31:0  |   ro   |   0x0   | PLAT_OWNER_AUTH_SLOT0_DIGEST |               |

## PLAT_OWNER_AUTH_SLOT1_DIGEST
Integrity digest for the PLAT_OWNER_AUTH_SLOT1 partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the PLAT_OWNER_AUTH_SLOT1 partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                           | Offset   |
|:-------------------------------|:---------|
| PLAT_OWNER_AUTH_SLOT1_DIGEST_0 | 0x12c    |
| PLAT_OWNER_AUTH_SLOT1_DIGEST_1 | 0x130    |


### Fields

```wavejson
{"reg": [{"name": "PLAT_OWNER_AUTH_SLOT1_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                         | Description   |
|:------:|:------:|:-------:|:-----------------------------|:--------------|
|  31:0  |   ro   |   0x0   | PLAT_OWNER_AUTH_SLOT1_DIGEST |               |

## PLAT_OWNER_AUTH_SLOT2_DIGEST
Integrity digest for the PLAT_OWNER_AUTH_SLOT2 partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the PLAT_OWNER_AUTH_SLOT2 partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                           | Offset   |
|:-------------------------------|:---------|
| PLAT_OWNER_AUTH_SLOT2_DIGEST_0 | 0x134    |
| PLAT_OWNER_AUTH_SLOT2_DIGEST_1 | 0x138    |


### Fields

```wavejson
{"reg": [{"name": "PLAT_OWNER_AUTH_SLOT2_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                         | Description   |
|:------:|:------:|:-------:|:-----------------------------|:--------------|
|  31:0  |   ro   |   0x0   | PLAT_OWNER_AUTH_SLOT2_DIGEST |               |

## PLAT_OWNER_AUTH_SLOT3_DIGEST
Integrity digest for the PLAT_OWNER_AUTH_SLOT3 partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the PLAT_OWNER_AUTH_SLOT3 partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name                           | Offset   |
|:-------------------------------|:---------|
| PLAT_OWNER_AUTH_SLOT3_DIGEST_0 | 0x13c    |
| PLAT_OWNER_AUTH_SLOT3_DIGEST_1 | 0x140    |


### Fields

```wavejson
{"reg": [{"name": "PLAT_OWNER_AUTH_SLOT3_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                         | Description   |
|:------:|:------:|:-------:|:-----------------------------|:--------------|
|  31:0  |   ro   |   0x0   | PLAT_OWNER_AUTH_SLOT3_DIGEST |               |

## ROM_PATCH_DIGEST
Integrity digest for the ROM_PATCH partition.
The integrity digest is 0 by default. Software must write this
digest value via the direct access interface in order to lock the partition.
After a reset, write access to the ROM_PATCH partition is locked and
the digest becomes visible in this CSR.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name               | Offset   |
|:-------------------|:---------|
| ROM_PATCH_DIGEST_0 | 0x144    |
| ROM_PATCH_DIGEST_1 | 0x148    |


### Fields

```wavejson
{"reg": [{"name": "ROM_PATCH_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name             | Description   |
|:------:|:------:|:-------:|:-----------------|:--------------|
|  31:0  |   ro   |   0x0   | ROM_PATCH_DIGEST |               |

## HW_CFG0_DIGEST
Integrity digest for the HW_CFG0 partition.
The integrity digest is 0 by default. The digest calculation can be triggered via the [`DIRECT_ACCESS_CMD.`](#direct_access_cmd)
After a reset, the digest then becomes visible in this CSR, and the corresponding partition becomes write-locked.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name             | Offset   |
|:-----------------|:---------|
| HW_CFG0_DIGEST_0 | 0x14c    |
| HW_CFG0_DIGEST_1 | 0x150    |


### Fields

```wavejson
{"reg": [{"name": "HW_CFG0_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name           | Description   |
|:------:|:------:|:-------:|:---------------|:--------------|
|  31:0  |   ro   |   0x0   | HW_CFG0_DIGEST |               |

## HW_CFG1_DIGEST
Integrity digest for the HW_CFG1 partition.
The integrity digest is 0 by default. The digest calculation can be triggered via the [`DIRECT_ACCESS_CMD.`](#direct_access_cmd)
After a reset, the digest then becomes visible in this CSR, and the corresponding partition becomes write-locked.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name             | Offset   |
|:-----------------|:---------|
| HW_CFG1_DIGEST_0 | 0x154    |
| HW_CFG1_DIGEST_1 | 0x158    |


### Fields

```wavejson
{"reg": [{"name": "HW_CFG1_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name           | Description   |
|:------:|:------:|:-------:|:---------------|:--------------|
|  31:0  |   ro   |   0x0   | HW_CFG1_DIGEST |               |

## SECRET0_DIGEST
Integrity digest for the SECRET0 partition.
The integrity digest is 0 by default. The digest calculation can be triggered via the [`DIRECT_ACCESS_CMD.`](#direct_access_cmd)
After a reset, the digest then becomes visible in this CSR, and the corresponding partition becomes write-locked.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name             | Offset   |
|:-----------------|:---------|
| SECRET0_DIGEST_0 | 0x15c    |
| SECRET0_DIGEST_1 | 0x160    |


### Fields

```wavejson
{"reg": [{"name": "SECRET0_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name           | Description   |
|:------:|:------:|:-------:|:---------------|:--------------|
|  31:0  |   ro   |   0x0   | SECRET0_DIGEST |               |

## SECRET1_DIGEST
Integrity digest for the SECRET1 partition.
The integrity digest is 0 by default. The digest calculation can be triggered via the [`DIRECT_ACCESS_CMD.`](#direct_access_cmd)
After a reset, the digest then becomes visible in this CSR, and the corresponding partition becomes write-locked.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name             | Offset   |
|:-----------------|:---------|
| SECRET1_DIGEST_0 | 0x164    |
| SECRET1_DIGEST_1 | 0x168    |


### Fields

```wavejson
{"reg": [{"name": "SECRET1_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name           | Description   |
|:------:|:------:|:-------:|:---------------|:--------------|
|  31:0  |   ro   |   0x0   | SECRET1_DIGEST |               |

## SECRET2_DIGEST
Integrity digest for the SECRET2 partition.
The integrity digest is 0 by default. The digest calculation can be triggered via the [`DIRECT_ACCESS_CMD.`](#direct_access_cmd)
After a reset, the digest then becomes visible in this CSR, and the corresponding partition becomes write-locked.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name             | Offset   |
|:-----------------|:---------|
| SECRET2_DIGEST_0 | 0x16c    |
| SECRET2_DIGEST_1 | 0x170    |


### Fields

```wavejson
{"reg": [{"name": "SECRET2_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name           | Description   |
|:------:|:------:|:-------:|:---------------|:--------------|
|  31:0  |   ro   |   0x0   | SECRET2_DIGEST |               |

## SECRET3_DIGEST
Integrity digest for the SECRET3 partition.
The integrity digest is 0 by default. The digest calculation can be triggered via the [`DIRECT_ACCESS_CMD.`](#direct_access_cmd)
After a reset, the digest then becomes visible in this CSR, and the corresponding partition becomes write-locked.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name             | Offset   |
|:-----------------|:---------|
| SECRET3_DIGEST_0 | 0x174    |
| SECRET3_DIGEST_1 | 0x178    |


### Fields

```wavejson
{"reg": [{"name": "SECRET3_DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name           | Description   |
|:------:|:------:|:-------:|:---------------|:--------------|
|  31:0  |   ro   |   0x0   | SECRET3_DIGEST |               |

## SW_CFG_WINDOW
Any read to this window directly maps to the corresponding offset in the creator and owner software
config partitions, and triggers an OTP readout of the bytes requested. Note that the transaction
will block until OTP readout has completed.

- Word Aligned Offset Range: `0x4000`to`0x7ffc`
- Size (words): `4096`
- Access: `ro`
- Byte writes are *not* supported.


<!-- END CMDGEN -->
