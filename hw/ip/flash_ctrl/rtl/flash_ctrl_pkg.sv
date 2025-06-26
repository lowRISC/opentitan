// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Controller generic package.
// This has no top-specific items so it is okay to use by generic IPs.

package flash_ctrl_pkg;
  // Parameters for keymgr.
  parameter int NumSeeds = 2;
  parameter bit [0:0] CreatorSeedIdx = 0;
  parameter bit [0:0] OwnerSeedIdx = 1;
  parameter int SeedWidth = 256;
  parameter int KeyWidth  = 128;
  typedef logic [KeyWidth-1:0] flash_key_t;

  // flash_ctrl to keymgr
  typedef struct packed {
    logic [NumSeeds-1:0][SeedWidth-1:0] seeds;
  } keymgr_flash_t;

  parameter keymgr_flash_t KEYMGR_FLASH_DEFAULT = '{
    seeds: '{
     256'h9152e32c9380a4bcc3e0ab263581e6b0e8825186e1e445631646e8bef8c45d47,
     256'hfa365df52da48cd752fb3a026a8e608f0098cfe5fa9810494829d0cd9479eb78
    }
  };

  // Flash Program Operations Supported
  typedef enum logic {
    FlashProgNormal = 0,
    FlashProgRepair = 1
  } flash_prog_e;
  parameter int ProgTypes = 2;

  // Flash partition type
  typedef enum logic {
    FlashPartData = 1'b0,
    FlashPartInfo = 1'b1
  } flash_part_e;

endpackage : flash_ctrl_pkg
