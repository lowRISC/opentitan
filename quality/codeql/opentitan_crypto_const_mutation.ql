// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * @name OpenTitan Crypto Const Field Mutation
 * @description Identifies casting away const on caller-owned capacity, configuration, or immutable pointer fields in OpenTitan crypto structs.
 * @kind problem
 * @problem.severity error
 * @id cpp/opentitan-crypto-const-capacity-mutation
 */

import cpp

from AddressOfExpr aoe, FieldAccess fa, Field f, PointerType pt
where
  aoe.getFile().getAbsolutePath().matches("%/sw/device/lib/crypto/%") and
  not aoe.getFile().getBaseName().matches("%unittest%") and
  fa = aoe.getOperand() and
  f = fa.getTarget() and
  f.getType().isConst() and
  pt = aoe.getFullyConverted().getType().stripTopLevelSpecifiers() and
  not pt.getBaseType().isConst()
select aoe,
  "Casting away const on '" + f.getDeclaringType().getName() + "::" + f.getName() +
    "' allows overwriting a caller-owned capacity, config, or immutable field."
