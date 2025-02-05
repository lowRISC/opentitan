# RACL Control Permission IP

`racl_ctrl` is currently being used in [top_darjeeling.hjson](../../../../hw/top_darjeeling/data/top_darjeeling.hjson).
There `racl_config` points to the main configuration file of the RACL Controller.
E.g., `racl_config: 'racl/racl.hjson'`.
Furthermore, each module instance that supports RACL must specify a valid `racl_mapping` for each of its `bus_interfaces`.
If there is only one such interface, the racl mapping may be specified as follows:
```
racl_mapping: 'racl/soc_rot_mapping.hjson'
```
whereas multiple `bus_interfaces` require a mapping for each interface:
```hjson
racl_mappings: {
    soc:  'racl/soc_rot_mapping.hjson'
    sram: 'racl/all_rd_wr_mapping.hjson'
}
```

## Example RACL configuration

```hjson
{
  // error_response controls whether to return TLUL error on RACL errors
  error_response: true
  // The CTN UID is transfered via the TLUL reserved user bits: rsvd[ctn_uid_bit_msb:ctn_uid_bit_lsb]
  ctn_uid_bit_lsb: 0
  ctn_uid_bit_msb: 4
  // The RACL role is transfered via the TLUL reserved user bits: rsvd[role_bit_msb:role_bit_lsb]
  role_bit_lsb: 5
  role_bit_msb: 8
  roles: {
    "ROT" :  { role_id: 0 }
    "ROLE1": { role_id: 1 }
    "SOC":   { role_id: 2 }
  }
  policies: {
    Null: [
      // Standard policies allowing all roles to access a register
      { name: "ALL_RD_WR"
        allowed_rd: [ "ROT", "ROLE1", "SOC" ]
        allowed_wr: [ "ROT", "ROLE1", "SOC" ]
      }
      // Standard policies allowing only the ROT role to access a register
      { name: "ROT_PRIVATE"
        rot_private: true
        allowed_rd: [ "ROT" ]
        allowed_wr: [ "ROT" ]
      }
      // Custom policy
      { name: "SOC_ROT"
        allowed_rd: [ "ROT", "SOC" ]
        allowed_wr: [ "ROT", "SOC" ]
      }
    ]
  }
}
```

## Example RACL mappings

A minimal example for a module that only uses registers (and no windows or ranges) can look as follows.
There the `*` maps to all registers.

```hjson
{
  Null: {
    registers: {
      "*": "SOC_ROT"
    }
  }
}
```

The `*` option does not exist for ranges. These must be explicitly defined as follows.

```hjson
{
  Null: {
    registers: {
      "*": "SOC_ROT"
    }
    windows: {
      "*": "SOC_ROT"
    }
    ranges: [
        {
            'base': "0x0000"
            'size': "0x1000"
            'policy': "ROT_PRIVATE"
        }
        {
            'base': "0x1000"
            'size': "0x0004"
            'policy': "ALL_RD_WR"
        }
    ]
  }
}
```

Mapping individual registers/windows is done like so (using the `mbx` as an example):

```hjson
{
  Null: {
    registers: {
      "SOC_CONTROL":           "SOC_ROT"
      "SOC_STATUS":            "SOC_ROT"
      "SOC_DOE_INTR_MSG_ADDR": "SOC_ROT"
      "SOC_DOE_INTR_MSG_DATA": "SOC_ROT"
    }
    windows: {
      "WDATA": "SOC_ROT"
      "RDATA": "SOC_ROT"
    }
  }
}
```
