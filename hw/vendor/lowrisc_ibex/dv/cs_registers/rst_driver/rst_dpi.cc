// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "register_environment.h"

#include "svdpi.h"

#include <map>
#include <string>

#ifdef __cplusplus
extern "C" {
#endif

static std::map<std::string, ResetDriver *> intfs;

void rst_register_intf(std::string name, ResetDriver *intf) {
  intfs.insert({name, intf});
}

void rst_deregister_intf(std::string name) { intfs.erase(name); }

void rst_tick(const char *name, svBit *rst_n) {
  auto ptr = intfs.find(name);
  if (ptr != intfs.end()) {
    ptr->second->DriveReset(rst_n);
  }
}

#ifdef __cplusplus
}
#endif
