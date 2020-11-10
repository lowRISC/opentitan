// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface kmac_sideload_if;
  // This struct contains three fields:
  // - valid
  // - key_share0
  // - key_share1
  keymgr_pkg::hw_key_req_t sideload_key;

endinterface
